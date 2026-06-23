import Extraction.Lean
import Batteries
open Std

namespace Lean.Meta.Grind.Extraction.AStar

abbrev Cost := Nat

structure CostNode where
  expr : Expr
  /-- The cost of only `expr` itself. In the context of `TopDownM` this is a lower bound cost
      estimate. In the context of `BottomUpM` this is the exact cost of the minimal cost term
      represented by `expr`. -/
  cost : Cost
  /-- The path cost up to but not including `expr` itself. -/
  pathCost : Cost

def CostNode.merit (n : CostNode) : Cost :=
  n.cost + n.pathCost

instance CostNode.instCoeExpr : Coe CostNode Expr where
  coe := expr

abbrev NodeQueue := Batteries.BinaryHeap CostNode (·.merit > ·.merit)

inductive ActionQueue.Action where
  | visit (node : CostNode)
  | assign (eqc : ExprPtr) (node : CostNode)

def ActionQueue.Action.node : Action → CostNode
  | visit node | assign _ node => node

abbrev ActionQueue := Batteries.BinaryHeap ActionQueue.Action (·.node.merit > ·.node.merit)

namespace TopDownM

structure Context where
  /-- The cost function which maps e-nodes (`Expr`) to a lower bound on the cost of an extracted
      term involving the given e-node. -/
  costFn : Expr → Cost

structure Result where
  /-- Given an e-node `ExprPtr`, indicates how many unresolved child e-classes it has. For example,
      for `f a b c`, if `mins` contains a value for `f` and `b`, but not `a` and `c`, then
      `delay[f a b c]? = 2`. Note that we only count *distinct* e-classes, so multiple references to
      values of the same e-class are counted only once. For example, in the example above, if `a`
      and `c` are in the same e-class, then `delay[f a b c]? = 1`. -/
  nodeDelay : HashMap ExprPtr Nat
  /-- Maps e-classes to the set of e-nodes which reference them. For example, if there are e-nodes
      `f a` and `g a`, then `parents[a]? = #[f a, g a]`. Note that we expect the given `ExprPtr` to
      be the `root` of the e-class. -/
  eqcParents : HashMap ExprPtr (Array ExprPtr)
  /-- Given a non-leaf e-node `ExprPtr`, records the minimal path cost from a root e-class to the
      e-node (not including the cost of the e-node itself). -/
  appPathCost : HashMap ExprPtr Cost
  /-- The set of leaf e-nodes (with associated costs). We store this as an `ActionQueue` as this
      will form the initial queue for the bottom-up phase (see `BottomUpM`). -/
  leaves : ActionQueue

structure State extends Result where
  /-- A priority queue used for scheduling e-nodes in a least-`merit`-first traversal of the
      e-graph. -/
  queue : NodeQueue
  /-- The set of e-classes who have been enqueued. This is used to avoid duplicate enqueuing of
      e-classes (and therefore their e-nodes). -/
  enqueuedEqcs : HashSet ExprPtr

instance : EmptyCollection State where
  emptyCollection := {
    nodeDelay := ∅, eqcParents := ∅, appPathCost := ∅, leaves := ∅, queue := ∅, enqueuedEqcs := ∅
  }

abbrev _root_.Lean.Meta.Grind.Extraction.AStar.TopDownM := StateT State <| ReaderT Context GoalM

def setNodeDelay (node : Expr) (num : Nat) : TopDownM Unit := do
  modify fun s => { s with nodeDelay := s.nodeDelay.insert ⟨node⟩ num }

def addEnqueuedEqc (eqc : ExprPtr) : TopDownM Unit := do
  modify fun s => { s with enqueuedEqcs := s.enqueuedEqcs.insert eqc }

def isEnqueuedEqc (eqc : ExprPtr) : TopDownM Bool := do
  let { enqueuedEqcs, .. } ← get
  return eqc ∈ enqueuedEqcs

def addEqcParent (eqc node : ExprPtr) : TopDownM Unit := do
  modify fun s =>
    let eqcParents := s.eqcParents.alter eqc fun
      | none    => #[node]
      | some ps => ps.push node
    { s with eqcParents }

def dequeue? : TopDownM (Option CostNode) := do
  let { queue, .. } ← get
  let (next?, queue) := queue.extractMax
  modify ({ · with queue })
  return next?

def enqueueNode (node : Expr) (pathCost : Cost) : TopDownM Unit := do
  let { costFn } ← read
  let cnode := { expr := node, cost := costFn node, pathCost }
  modify fun s => { s with queue := s.queue.insert cnode }

def enqueueEqc (eqc : ExprPtr) (eqcPathCost : Cost) : TopDownM Unit := do
  unless ← isEnqueuedEqc eqc do
    let nodes ← getEqc eqc.expr
    for node in nodes do
      enqueueNode node eqcPathCost
    addEnqueuedEqc eqc

def setAppPathCost (cnode : CostNode) : TopDownM Unit := do
  modify fun s => { s with appPathCost := s.appPathCost.insert ⟨cnode⟩ cnode.pathCost }

def addLeaf (cnode : CostNode) : TopDownM Unit := do
  modify fun s => { s with leaves := s.leaves.insert (.visit cnode) }

def visitAppNode (cnode : CostNode) : TopDownM Unit := do
  setAppPathCost cnode
  cnode.expr.withApp fun fn args => do
    let mut uniqueChildEqcs : HashSet ExprPtr := {}
    for child in #[fn] ++ args do
      -- If `child` is an internalized node.
      if let some eqc ← getRootPtr? child then
        unless eqc ∈ uniqueChildEqcs do
          uniqueChildEqcs := uniqueChildEqcs.insert eqc
          addEqcParent eqc ⟨cnode⟩
          -- Note: `enqueueEqc` ensures that an e-class is not enqueued multiple times.
          enqueueEqc eqc cnode.merit
    setNodeDelay cnode uniqueChildEqcs.size

def visitNode (cnode : CostNode) : TopDownM Unit := do
  if cnode.expr.isApp then
    visitAppNode cnode
  else
    addLeaf cnode

/--
The goal of the top-down step is to:
(1) compute the minimal path cost for each e-node (`minPathCost`)
(2) record the parents of each e-class (`eqcParents`)
(3) record the number of unique child e-class of each e-node (`nodeDelay`)
-/
def main (target : ExprPtr) : TopDownM Unit := do
  -- **NOTE** We visit more e-nodes/edges than would be necessary for just establishing the minimal
  --          path cost of each e-class, as we need to ensure that the `parents` and `delay` fields
  --          are complete. I believe this will not be necessary in *interleaved* A* extraction.
  enqueueEqc target 0
  while let some cnode ← dequeue? do visitNode cnode

nonrec def run (target : ExprPtr) (costFn : Expr → Cost) : GoalM Result := do
  let (_, s) ← main target |>.run ∅ |>.run { costFn }
  return s.toResult

end TopDownM

namespace BottomUpM

structure Context where
  /-- The cost function which maps e-nodes (`Expr`) to the cost of extracting a term from it
      assuming the children has given costs (`Array Cost`). -/
  costFn : Expr → Array Cost → Cost
  /-- The minimal path costs of non-leaf e-nodes (not including the cost of the e-node itself). -/
  appPathCost : HashMap ExprPtr Cost
  /-- Maps e-classes to the set of e-nodes which reference them. For example, if there are e-nodes
      `f a` and `g a`, then `parents[a]? = #[f a, g a]`. Note that we expect the given `ExprPtr` to
      be the `root` of the e-class. -/
  eqcParents : HashMap ExprPtr (Array ExprPtr)

structure Result where
  /-- Records the minimal e-node for each e-class. Note that we expect the given `ExprPtr` to be the
      `root` of the e-class. The cost associated with each e-node is the the cost which its minimal
      representation *will* have when/if constructed. -/
  eqcMin : HashMap ExprPtr (Expr × Cost)

structure Init where
  queue : ActionQueue
  /-- Given an e-node `ExprPtr`, indicates how many unresolved child e-classes it has. For example,
      for `f a b c`, if `mins` contains a value for `f` and `b`, but not `a` and `c`, then
      `delay[f a b c]? = 2`. Note that we only count *distinct* e-classes, so multiple references to
      values of the same e-class are counted only once. For example, in the example above, if `a`
      and `c` are in the same e-class, then `delay[f a b c]? = 1`. -/
  nodeDelay : HashMap ExprPtr Nat

structure State extends Result, Init

abbrev _root_.Lean.Meta.Grind.Extraction.AStar.BottomUpM := StateT State <| ReaderT Context GoalM

def eqcHasMin (eqc : ExprPtr) : BottomUpM Bool := do
  let { eqcMin, .. } ← get
  return eqc ∈ eqcMin

def setEqcMin (eqc : ExprPtr) (node : Expr) (cost : Cost) : BottomUpM Unit := do
  modify fun s => { s with eqcMin := s.eqcMin.insert eqc (node, cost) }

def setNodeDelay (node : ExprPtr) (delay : Nat) : BottomUpM Unit :=
  modify fun s => { s with nodeDelay := s.nodeDelay.insert node delay }

def enqueue (action : ActionQueue.Action) : BottomUpM Unit := do
  modify fun s => { s with queue := s.queue.insert action }

def dequeue? : BottomUpM (Option ActionQueue.Action) := do
  let { queue, .. } ← get
  let (next?, queue) := queue.extractMax
  modify ({ · with queue })
  return next?

/--
Computes the minimal cost of the given e-node. This should only be called when all of the `node`'s
child e-classes are resolved (have a value in `eqcMin`).
-/
def getMinNodeCost (node : Expr) : BottomUpM Cost := do
  let { costFn, .. } ← read
  let { eqcMin, .. } ← get
  node.withApp fun fn args => do
    let children := #[fn] ++ args
    let childCosts ← children.mapM fun child => do
      -- For non-internalized children, we compute the cost directly.
      -- **TODO** Should we cache the costs of non-internalized expressions?
      let some eqc ← getRootPtr? child | return costFn child #[]
      let (_, cost) := eqcMin[eqc]!
      return cost
    return costFn node childCosts

/-- This should only be called when all child e-classes of `node` have a value in `eqcMin`. -/
def enqueueAppNodeVisit (node : ExprPtr) : BottomUpM Unit := do
  let { appPathCost, .. } ← read
  let pathCost := appPathCost[node]!
  let cost ← getMinNodeCost node.expr
  let cnode := { expr := node.expr, cost, pathCost }
  enqueue (.visit cnode)

def updateEqcParents (eqc : ExprPtr) : BottomUpM Unit := do
  let { eqcParents, .. } ← read
  let { nodeDelay, .. } ← get
  let some parents := eqcParents[eqc]? | return
  for parentNode in parents do
    let some (delay + 1) := nodeDelay[parentNode]? | panic! "Reached bad path in `updateEqcParents`."
    -- Note: When `delay = 0`, we don't update `nodeDelay` as the e-node is resolved anyway.
    if delay = 0 then
      -- The `parentNode` must be an `.app` (had children), otherwise it could (should) never have
      -- been a parent of `eqc`.
      enqueueAppNodeVisit parentNode
    else
      setNodeDelay parentNode delay

def assignEqc (eqc : ExprPtr) (cnode : CostNode) : BottomUpM Unit := do
  unless ← eqcHasMin eqc do
    setEqcMin eqc cnode.expr cnode.cost
    updateEqcParents eqc

def visitNode (cnode : CostNode) : BottomUpM Unit := do
  let eqc ← getRootPtr cnode
  enqueue (.assign eqc cnode)

def runAction : ActionQueue.Action → BottomUpM Unit
  | .visit cnode      => visitNode cnode
  | .assign eqc cnode => assignEqc eqc cnode

def main (target : ExprPtr) : BottomUpM Unit := do
  while let some action ← dequeue? do
    runAction action
    if ← eqcHasMin target then break

nonrec def run (target : ExprPtr) (ctx : Context) (init : Init) : GoalM Result := do
  let (_, s) ← main target |>.run { init with eqcMin := ∅ } |>.run ctx
  return s.toResult

end BottomUpM

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
    modify ({ · with cache := cache.insert eqc e })
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

/--
A cost function assigns a cost to an e-node (`Expr`) given the costs of its children `Array Cost`.
If the child costs are not provided, i.e. they are `none`, then the function should return a lower
bound on the cost of the enode. For example, if we know that a head symbol `f` always incurs a cost
of `1`, then an application of `f` should return a lower cost bound of `1`.
-/
abbrev CostFn := Expr → Option (Array Cost) → Cost

def CostFn.approx (costFn : CostFn) (e : Expr) : Cost :=
  costFn e none

def CostFn.exact (costFn : CostFn) (e : Expr) (cs : Array Cost) : Cost :=
  costFn e cs

def extract (target : Expr) (costFn : CostFn) : GoalM Expr := do
  let target ← getRootPtr target
  let { nodeDelay, eqcParents, appPathCost, leaves } ← TopDownM.run target costFn.approx
  let { eqcMin } ← BottomUpM.run target { costFn := costFn.exact, appPathCost, eqcParents } { queue := leaves, nodeDelay }
  ConstructM.run target { eqcMin }
