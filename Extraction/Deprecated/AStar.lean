import Extraction.Lean
import Extraction.Cost
import Batteries
open Std

namespace Lean.Meta.Grind.Extraction.AStar

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

abbrev Queue := Batteries.BinaryHeap CostNode (·.merit > ·.merit)

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
  /-- The set of leaf e-nodes (with associated costs). We store this as a `Queue` as this will form
      the initial queue for the bottom-up phase (see `BottomUpM`). -/
  leaves : Queue

structure State extends Result where
  /-- A priority queue used for scheduling e-nodes in a least-`minPathCost`-first traversal of the
      e-graph. -/
  queue : Queue
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
  modify fun s => { s with leaves := s.leaves.insert cnode }

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
def main (target : Expr) : TopDownM Unit := do
  -- **NOTE** We visit more e-nodes/edges than would be necessary for just establishing the minimal
  --          path cost of each e-class, as we need to ensure that the `parents` and `delay` fields
  --          are complete. I believe this will not be necessary in *interleaved* A* extraction.
  let target ← getRootPtr target
  enqueueEqc target 0
  while let some cnode ← dequeue? do visitNode cnode

nonrec def run (target : Expr) (costFn : Expr → Cost) : GoalM Result := do
  let (_, s) ← main target |>.run ∅ |>.run { costFn }
  return s.toResult

end TopDownM

namespace BottomUpM

-- ...
