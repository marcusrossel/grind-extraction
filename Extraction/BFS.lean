import Extraction.Lean
open Std

namespace Lean.Meta.Grind.Extraction.BFS

/--
A cost function assigns a cost to an e-node (`Expr`) given the costs of its children `Array Nat`.
-/
abbrev CostFn := Expr → (Array Nat) → Nat

namespace ExtractM

structure State where
  /-- A FIFO queue used for scheduling e-nodes in a BFS-style traversal of the e-graph. -/
  queue : Queue Expr
  /-- The set of e-classes who have already been enqueued. -/
  visitedEqcs : HashSet ExprPtr
  /-- Maps e-classes to the set of e-nodes which reference them. Note that this map is not complete.
      When an e-node is visited, we register the e-node as a parent only for its child e-classes
      which are *unresolved* (do not have an entry in `eqcMin`). -/
  eqcParents : HashMap ExprPtr (Array ExprPtr)
  /-- Maps e-classes to the number of e-nodes they are waiting on in order to resolve. -/
  eqcDelay : HashMap ExprPtr Nat
  /-- Maps e-nodes to the number of e-classes they are waiting on in order to resolve. -/
  nodeDelay : HashMap ExprPtr Nat
  /-- Maps e-classes to their minimal cost e-node and the associated cost. -/
  eqcMin : HashMap ExprPtr (ExprPtr × Nat)
  /-- Maps e-nodes to their minimal cost. -/
  nodeMin : HashMap ExprPtr Nat

instance State.instEmptyCollection : EmptyCollection State where
  emptyCollection := {
    queue := ∅, visitedEqcs := ∅, eqcParents := ∅,
    eqcDelay := ∅, nodeDelay := ∅, eqcMin := ∅, nodeMin := ∅
  }

abbrev _root_.Lean.Meta.Grind.Extraction.ExtractM := StateT State <| ReaderT CostFn GoalM

def eqcIsVisited (eqc : ExprPtr) : ExtractM Bool := do
  let { visitedEqcs, .. } ← get
  return eqc ∈ visitedEqcs

def setVisitedEqc (eqc : ExprPtr) : ExtractM Unit := do
  modify fun s => { s with visitedEqcs := s.visitedEqcs.insert eqc }

def setEqcDelay (eqc : ExprPtr) (delay : Nat) : ExtractM Unit :=
  modify fun s => { s with eqcDelay := s.eqcDelay.insert eqc delay }

def setNodeDelay (node : ExprPtr) (delay : Nat) : ExtractM Unit :=
  modify fun s => { s with nodeDelay := s.nodeDelay.insert node delay }

def addEqcParent (eqc parent : ExprPtr) : ExtractM Unit :=
  modify fun s =>
    let eqcParents := s.eqcParents.alter eqc fun
      | none         => #[parent]
      | some parents => parents.push parent
    { s with eqcParents }

def dequeue? : ExtractM (Option Expr) := do
  let { queue, .. } ← get
  let some (e, queue) := queue.dequeue? | return none
  modify ({ · with queue })
  return e

def enqueueNode (node : Expr) : ExtractM Unit :=
  modify fun s => { s with queue := s.queue.enqueue node }

/--
Enqueues all e-nodes in the given e-class while also:
(1) respecting and updating `visitedEqcs` (no e-class is enqueued more than once), and
(2) setting the `eqcDelay` for the given e-class.
-/
def enqueueEqc (eqc : ExprPtr) : ExtractM Unit := do
  unless ← eqcIsVisited eqc do
    let nodes ← getEqc eqc.expr
    nodes.forM enqueueNode
    -- When an e-class is being visited for the first time (which we assert by the check above),
    -- then it must be waiting on all of its e-nodes, as these e-nodes could not have been reached
    -- any other way.
    setEqcDelay eqc nodes.length
    setVisitedEqc eqc

/--
Gets the minimum cost e-node in the given e-class. This should only be called when all of the
`ecq`'s e-nodes are resolved (have a value in `nodeMin`).
-/
def getMinNodeInEqc (eqc : ExprPtr) : ExtractM (ExprPtr × Nat) := do
  let { nodeMin, .. } ← get
  -- We split the list of e-nodes into head and tail immediately, so we have a sensible value to
  -- initialize `minNodes` and `minCost` with, below.
  let node :: nodes ← getEqc eqc.expr | panic! "Found empty e-class in `getMinNode`."
  let mut minNode := node
  let mut minCost := nodeMin[(⟨node⟩ : ExprPtr)]!
  for node in nodes do
    let cost := nodeMin[(⟨node⟩ : ExprPtr)]!
    if cost < minCost then
      minNode := node
      minCost := cost
  return (⟨minNode⟩, minCost)

/--
Computes the minimal cost of the given e-node. This should only be called when all of the `node`'s
child e-classes are resolved (have a value in `eqcMin`).
-/
def getMinNodeCost (node : Expr) : ExtractM Nat := do
  let costFn ← read
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

mutual

/--
Decrements the delay each of `eqc`'s parent e-nodes. If the delay becomes `0`, computes and sets the
e-node's minimal cost, which may induce futher updates. See `setNodeMin` for details on which
updates are propagated.
-/
partial def updateEqcParents (eqc : ExprPtr) : ExtractM Unit := do
  let { eqcParents, nodeDelay, .. } ← get
  let some parents := eqcParents[eqc]? | return
  for parentNode in parents do
    let some (delay + 1) := nodeDelay[parentNode]? | panic! "Reached bad path in `updateEqcParents`."
    -- Note: When `delay = 0`, we don't update `nodeDelay` as the e-node is resolved anyway.
    if delay = 0 then
      -- The `parentNode` must be an `.app` (had children), otherwise it could (should) never have
      -- been a parent of `eqc`.
      let cost ← getMinNodeCost parentNode.expr
      setNodeMin parentNode cost
    else
      setNodeDelay parentNode delay

/--
Sets the value of `eqcMin[eqc]` to be the minimum of all e-nodes in `eqc`. Then updates all of
`eqc`'s parent e-nodes, which may induce further updates. See `updateEqcParents` for details on
which updates are propagated.

This should only be called when all of the `ecq`'s e-nodes are resolved (have a value in `nodeMin`).
-/
partial def setEqcMin (eqc : ExprPtr) : ExtractM Unit := do
  let min ← getMinNodeInEqc eqc
  modify fun s => { s with eqcMin := s.eqcMin.insert eqc min }
  updateEqcParents eqc

/--
Decrements the delay of the given `node`'s parent e-class. If the delay becomes `0`, sets the
e-class's minimum e-node, which may induce futher updates. See `setEqcMin` for details on which
updates are propagated.
-/
partial def updateNodeParent (node : Expr) : ExtractM Unit := do
  let { eqcDelay, .. } ← get
  let parentEqc ← getRootPtr node
  let some (delay + 1) := eqcDelay[parentEqc]? | panic! "Reached bad path in `updateNodeParent`."
  -- Note: When `delay = 0`, we don't update `eqcDelay` as the e-class is resolved anyway.
  if delay = 0 then
    setEqcMin parentEqc
  else
    setEqcDelay parentEqc delay

/--
Sets the minimal cost of the given `node` and runs all required updates afterwards. That is, the
`node`'s parent e-class's delay is reduced, which may induce further updates. See `updateNodeParent`
for details on which updates are propagated.
-/
partial def setNodeMin (node : ExprPtr) (cost : Nat) : ExtractM Unit := do
  modify fun s => { s with nodeMin := s.nodeMin.insert node cost }
  updateNodeParent node.expr

end

def visitAppNode (node : Expr) : ExtractM Unit := do
  node.withApp fun fn args => do
    let costFn ← read
    let { eqcMin, .. } ← get
    let mut childCosts := #[]
    let mut childEqcs : Array ExprPtr := ∅
    let mut delay := 0
    for child in #[fn] ++ args do
      -- If `child` is an internalized node.
      if let some eqc ← getRootPtr? child then
        -- We need to ensure that we do not traverse the same e-class twice, as otherwise the delays
        -- (`nodeDelay`) will be broken.
        unless childEqcs.contains eqc do
          childEqcs := childEqcs.push eqc
          -- If the child `eqc` is already resolved, remember its cost. If it is not resolved, add
          -- it to the `delay` and remember that `node` is a parent waiting for it.
          if let some (_, cost) := eqcMin[eqc]? then
            childCosts := childCosts.push cost
          else
            delay := delay + 1
            addEqcParent eqc ⟨node⟩
      else
        -- We treat non-internalized children like leaf nodes.
        -- **TODO** Should we cache the costs of non-internalized expressions?
        childCosts := childCosts.push (costFn child #[])
    -- If the `delay` is still `0` after traversing all children, that means that all child
    -- e-classes are already resolved, so the e-node is resolvable. Otherwise, we enqueue all
    -- unresolved e-classes.
    if delay = 0 then
      setNodeMin ⟨node⟩ (costFn node childCosts)
    else
      setNodeDelay ⟨node⟩ delay
      childEqcs.forM enqueueEqc

def visitNode (node : Expr) : ExtractM Unit := do
  if node.isApp then
    visitAppNode node
  else
    let costFn ← read
    setNodeMin ⟨node⟩ (costFn node #[])

nonrec def run (costFn : CostFn) (k : ExtractM α) : GoalM α := do
  Prod.fst <$> k.run ∅ |>.run costFn

end ExtractM

namespace ConstructM

/--
Adds a cache on `ExtractM` mapping e-classes to expressions, used hen construction of the final
extracted expression.
-/
abbrev ConstructM := StateT (HashMap ExprPtr Expr) ExtractM

def getMinNode (eqc : ExprPtr) : ConstructM Expr := do
  let { eqcMin, .. } ← getThe ExtractM.State
  return eqcMin[eqc]!.fst.expr

def withCache (eqc : ExprPtr) (k : ConstructM Expr) : ConstructM Expr := do
  let cache ← get
  if let some e := cache[eqc]? then
    return e
  else
    let e ← k
    modify (·.insert eqc e)
    return e

partial def construct (eqcMem : Expr) : ConstructM Expr := do
  -- If the expression is not internalized, we return it as is.
  let some eqc ← getRootPtr? eqcMem | return eqcMem
  withCache eqc do
    let node ← getMinNode eqc
    if node.isApp then
      node.traverseApp construct
    else
      return node

nonrec def run (k : ConstructM α) : ExtractM α := do
  Prod.fst <$> k.run ∅

end ConstructM

def extract (target : Expr) (costFn : CostFn) : GoalM Expr := open ExtractM ConstructM in do
  ExtractM.run costFn do
    let eqc ← getRootPtr target
    enqueueEqc eqc
    while let some node ← dequeue? do visitNode node
    ConstructM.run do construct target
