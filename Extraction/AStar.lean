import Extraction.Lean
import Batteries
open Std

namespace Lean.Meta.Grind.Extraction.AStar

abbrev Cost := Nat

abbrev CostFn := Expr → Option (Array Cost) → Cost

def CostFn.approx (costFn : CostFn) (e : Expr) : Cost :=
  costFn e none

def CostFn.exact (costFn : CostFn) (e : Expr) (cs : Array Cost) : Cost :=
  costFn e cs

structure CostNode where
  expr : Expr
  /-- The cost of only `expr` itself. In the context of `.visit` actions, this is a lower bound cost
      estimate. In the context of `.assign` actions, this is the exact cost of the minimal cost term
      represented by `expr`. -/
  cost : Cost
  /-- The path cost up to but not including `expr` itself. -/
  pathCost : Cost

def CostNode.merit (n : CostNode) : Cost :=
  n.cost + n.pathCost

instance CostNode.instCoeExpr : Coe CostNode Expr where
  coe := expr

inductive Action where
  | visit (node : CostNode)
  | assign (eqc : ExprPtr) (node : CostNode)

def Action.node : Action → CostNode
  | visit node | assign _ node => node

abbrev Queue := Batteries.BinaryHeap Action (·.node.merit > ·.node.merit)

namespace SearchM

structure Context where
  costFn : CostFn

structure State where
  queue : Queue
  /-- The set of e-classes who have been enqueued. This is used to avoid duplicate enqueuing of
      e-classes (and therefore their e-nodes). -/
  enqueuedEqcs : HashSet ExprPtr
  /-- Given an e-node `ExprPtr`, indicates how many unresolved child e-classes it has. For example,
      for `f a b c`, if `mins` contains a value for `f` and `b`, but not `a` and `c`, then
      `delay[f a b c]? = 2`. Note that we only count *distinct* e-classes, so multiple references to
      values of the same e-class are counted only once. For example, in the example above, if `a`
      and `c` are in the same e-class, then `delay[f a b c]? = 1`. -/
  nodeDelay : HashMap ExprPtr Nat
  /-- Maps e-classes to the set of e-nodes which reference them. For example, if there are e-nodes
      `f a` and `g a`, then `parents[a]? = #[f a, g a]`. Note that we expect the given `ExprPtr` to
      be the `root` of the e-class. -/
  eqcParents : HashMap ExprPtr (Array CostNode)
  /-- Records the minimal e-node for each e-class. Note that we expect the given `ExprPtr` to be the
      `root` of the e-class. The cost associated with each e-node is the the cost which its minimal
      representation *will* have when/if constructed. -/
  eqcMin : HashMap ExprPtr (Expr × Cost)

instance : EmptyCollection State where
  emptyCollection := {
    queue := ∅, enqueuedEqcs := ∅, nodeDelay := ∅, eqcParents := ∅, eqcMin := ∅
  }

abbrev _root_.Lean.Meta.Grind.Extraction.AStar.SearchM := StateT State <| ReaderT Context GoalM

def eqcHasMin (eqc : ExprPtr) : SearchM Bool := do
  let { eqcMin, .. } ← get
  return eqc ∈ eqcMin

def setEqcMin (eqc : ExprPtr) (node : Expr) (cost : Cost) : SearchM Unit := do
  modify fun s => { s with eqcMin := s.eqcMin.insert eqc (node, cost) }

def setNodeDelay (node : Expr) (num : Nat) : SearchM Unit := do
  modify fun s => { s with nodeDelay := s.nodeDelay.insert ⟨node⟩ num }

/-- Marks the given e-class as already having been enqueued before (via `enqueueEqc`). -/
def addEnqueuedEqc (eqc : ExprPtr) : SearchM Unit := do
  modify fun s => { s with enqueuedEqcs := s.enqueuedEqcs.insert eqc }

def isEnqueuedEqc (eqc : ExprPtr) : SearchM Bool := do
  let { enqueuedEqcs, .. } ← get
  return eqc ∈ enqueuedEqcs

def addEqcParent (eqc : ExprPtr) (cnode : CostNode) : SearchM Unit := do
  modify fun s =>
    let eqcParents := s.eqcParents.alter eqc fun
      | none    => #[cnode]
      | some ps => ps.push cnode
    { s with eqcParents }

/-- Dequeues the lowest-cost action (using the action's `node`'s `merit`) from the queue. -/
def dequeue? : SearchM (Option Action) := do
  let { queue, .. } ← get
  let (next?, queue) := queue.extractMax
  modify ({ · with queue })
  return next?

/-- Adds a given action to the queue. -/
def enqueue (action : Action) : SearchM Unit := do
  modify fun s => { s with queue := s.queue.insert action }

/-- Adds a `.visit`-action for the given e-node to the queue. -/
def enqueueVisitNode (node : Expr) (pathCost : Cost) : SearchM Unit := do
  let { costFn } ← read
  let cnode := { expr := node, cost := costFn.approx node, pathCost }
  enqueue (.visit cnode)

/-- Adds a `.assign`-action for the given e-node (its e-class) to the queue. -/
def enqueueAssignment (cnode : CostNode) (childCosts : Array Cost) : SearchM Unit := do
  let { costFn } ← read
  let eqc ← getRootPtr cnode
  let cnode := { cnode with cost := costFn.exact cnode childCosts }
  enqueue (.assign eqc cnode)

/-- Adds `.visit`-actions for all e-nodes in the given e-class to the queue. -/
def enqueueVisitEqc (eqc : ExprPtr) (eqcPathCost : Cost) : SearchM Unit := do
  unless ← isEnqueuedEqc eqc do
    let nodes ← getEqc eqc.expr
    for node in nodes do
      enqueueVisitNode node eqcPathCost
    addEnqueuedEqc eqc

def visitAppNode (cnode : CostNode) : SearchM Unit := do
  cnode.expr.withApp fun fn args => do
    let { costFn } ← read
    let { eqcMin, .. } ← get
    let mut childCosts := #[]
    let mut delayedEqcs : HashSet ExprPtr := ∅
    for child in #[fn] ++ args do
      -- If `child` is an internalized node.
      if let some eqc ← getRootPtr? child then
        -- (1) If the child `eqc` is already resolved, remember its cost.
        -- (2) If `eqc` is not resolved, set the parent-child relationship, set the node delay
        --     (after the for-loop) and enqueue `eqc`.
        if let some (_, cost) := eqcMin[eqc]? then
          childCosts := childCosts.push cost
        else if eqc ∉ delayedEqcs then
          -- It is important that we do not register the same e-class as delayed multiple times, as
          -- this would break the `delay` count.
          delayedEqcs := delayedEqcs.insert eqc
          addEqcParent eqc cnode
          -- Note: `enqueueEqc` ensures that an e-class is not enqueued multiple times.
          enqueueVisitEqc eqc cnode.merit
      else
        -- We treat non-internalized children like leaf nodes.
        -- **TODO** Should we cache the costs of non-internalized expressions?
        childCosts := childCosts.push <| costFn.exact child #[]
    if delayedEqcs.size = 0 then
      -- If all `cnode` children are resolved, we can add an `.assign`-action for it immediately.
      enqueueAssignment cnode childCosts
    else
      setNodeDelay cnode delayedEqcs.size

def visitNode (cnode : CostNode) : SearchM Unit := do
  if cnode.expr.isApp then
    visitAppNode cnode
  else
    -- Visiting a leaf node immediately causes an `.assign`-action to be generated for that node.
    enqueueAssignment cnode #[]

def nodeChildCosts (node : Expr) : SearchM (Array Cost) := do
  let { costFn, .. } ← read
  let { eqcMin, .. } ← get
  node.withApp fun fn args => do
    let children := #[fn] ++ args
    children.mapM fun child => do
      -- For non-internalized children, we compute the cost directly.
      -- **TODO** Should we cache the costs of non-internalized expressions?
      let some eqc ← getRootPtr? child | return costFn.exact child #[]
      let (_, cost) := eqcMin[eqc]!
      return cost

def updateEqcParents (eqc : ExprPtr) : SearchM Unit := do
  let { eqcParents, nodeDelay, .. } ← get
  let some parents := eqcParents[eqc]? | return
  for parentNode in parents do
    let some (delay + 1) := nodeDelay[(⟨parentNode⟩ : ExprPtr)]?
      | panic! "Reached bad path in `updateEqcParents`."
    -- Note: When `delay = 0`, we don't update `nodeDelay` as the e-node is resolved anyway.
    if delay = 0 then
      -- The `parentNode` must be an `.app` (had children), otherwise it could (should) never have
      -- been a parent of `eqc`.
      let childCosts ← nodeChildCosts parentNode
      enqueueAssignment parentNode childCosts
    else
      setNodeDelay parentNode delay

def assignEqc (eqc : ExprPtr) (cnode : CostNode) : SearchM Unit := do
  unless ← eqcHasMin eqc do
    setEqcMin eqc cnode.expr cnode.cost
    updateEqcParents eqc

def runAction : Action → SearchM Unit
  | .visit cnode      => visitNode cnode
  | .assign eqc cnode => assignEqc eqc cnode

def main (target : ExprPtr) : SearchM Unit := do
  enqueueVisitEqc target 0
  while let some action ← dequeue? do
    runAction action
    if ← eqcHasMin target then break

nonrec def run (target : ExprPtr) (costFn : CostFn) : GoalM (HashMap ExprPtr (Expr × Cost)) := do
  let (_, s) ← main target |>.run ∅ |>.run { costFn }
  return s.eqcMin

end SearchM

namespace ConstructM

structure Context where
  eqcMin : HashMap ExprPtr (Expr × Cost)

structure State where
  cache : HashMap ExprPtr Expr

instance : EmptyCollection State where
  emptyCollection := { cache := ∅ }

abbrev _root_.Lean.Meta.Grind.Extraction.AStar.ConstructM := StateT State <| ReaderT Context <| GoalM

def getMinNode (eqc : ExprPtr) : ConstructM Expr := do
  let { eqcMin } ← read
  return eqcMin[eqc]!.fst

def withCache (eqc : ExprPtr) (k : ConstructM Expr) : ConstructM Expr := do
  let { cache } ← get
  if let some e := cache[eqc]? then
    return e
  else
    let e ← k
    modify fun s => { s with cache := s.cache.insert eqc e }
    return e

partial def main (eqcMem : Expr) : ConstructM Expr := do
  -- If the expression is not internalized, we return it as is.
  let some eqc ← getRootPtr? eqcMem | return eqcMem
  withCache eqc do
    let node ← getMinNode eqc
    if node.isApp then
      node.traverseApp main
    else
      return node

nonrec def run (target : ExprPtr) (ctx : Context) : GoalM Expr :=
  Prod.fst <$> do main target.expr |>.run ∅ |>.run ctx

end ConstructM

def extract (target : Expr) (costFn : CostFn) : GoalM Expr := do
  let target ← getRootPtr target
  let eqcMin ← SearchM.run target costFn
  ConstructM.run target { eqcMin }
