import Extraction.Lean
import Extraction.Sketch
import Batteries
open Std Lean Meta Elab Term Tactic Grind
open Batteries (BinaryHeap)

namespace Lean.Meta.Grind.Extraction

structure SizedExpr where
  expr : Expr
  size : Nat
  deriving Inhabited

instance SizedExpr.instToMessageData : ToMessageData SizedExpr where
  toMessageData e := m!"[{e.size}] {e.expr}"

def _root_.Lean.Expr.toSized (e : Expr) : SizedExpr where
  expr := e
  size := e.sizeWithoutSharing

abbrev ExtractM.Queue := BinaryHeap SizedExpr (·.size > ·.size)

structure ExtractM.State where
  /-- Records the (current) minimal representatives for e-classes. Note that we expect the given
      `ExprPtr` to be the `root` of the e-class. -/
  mins : HashMap ExprPtr SizedExpr
  /-- Given an e-node `ExprPtr`, indicates how many unresolved child e-classes it has. For example,
      for `f a b c`, if `mins` contains a value for `f` and `b`, but not `a` and `c`, then
      `pending[f a b c]? = 2`. Note that we only count *distinct* e-classes, so multiple
      references to values of the same e-class are counted only once. For example, in the example
      above, if `a` and `c` are in the same e-class, then `pending[f a b c]? = 1`. -/
  pending : HashMap ExprPtr Nat
  /-- Maps e-classes to the set of e-nodes which reference them. For example, if there are e-nodes
      `f a` and `g a`, then `parents[a]? = #[f a, g a]`. Note that we expect the given `ExprPtr` to
      be the `root` of the e-class. -/
  parents : HashMap ExprPtr (Array ExprPtr)
  queue : Queue

instance ExtractM.State.instEmptyCollection : EmptyCollection State where
  emptyCollection := { mins := ∅, parents := ∅, pending := ∅, queue := ∅ }

abbrev ExtractM := StateT ExtractM.State GoalM

namespace ExtractM

def setPending (node : Expr) (num : Nat) : ExtractM Unit := do
  modify fun s => { s with pending := s.pending.insert ⟨node⟩ num }

/-- Implementation detail of `resolvePending`. -/
def nodeSize! (node : ExprPtr) : ExtractM Nat := do
  let { mins, .. } ← get
  node.expr.withApp fun fn args => do
    let mut size := 0
    for e in #[fn] ++ args do
      -- This skips non-internalized expressions.
      let some child ← getENode? e | continue
      let eqc : ExprPtr := ⟨child.root⟩
      size := size + mins[eqc]!.size
    return size

/--
Propagates the changes to `State.pending` and `State.queue` which should follow from the given
e-class `eqc` having a (newly set) minimum:
(1) Each parent e-node of `eqc` has its `pending` count reduced by `1`.
(2) If Step 1 reduces any `pending` count to `0`, the corresponding e-node is enqueued.
-/
def resolvePending (eqc : Expr) : ExtractM Unit := do
  let eqc : ExprPtr := ⟨eqc⟩
  let s ← get
  let some eqcParents := s.parents[eqc]? | return
  let mut pending := s.pending
  let mut queue := s.queue
  for parent in eqcParents do
    let some (num + 1) := pending[parent]? | continue
    pending := pending.insert parent num
    if num = 0 then
      -- This is not the size of `parent.expr`, but rather the size which its minimal representation
      --  *will* have when/if constructed.
      let size ← nodeSize! parent
      queue := queue.insert { parent with size }
  modify ({ · with pending, queue })

def addParent (eqc node : Expr) : ExtractM Unit := do
  modify fun s =>
    let parents := s.parents.alter ⟨eqc⟩ fun
      | none    => #[(⟨node⟩ : ExprPtr)]
      | some ps => ps.push ⟨node⟩
    { s with parents }

def enqueue (node : SizedExpr) : ExtractM Unit := do
  modify fun s => { s with queue := s.queue.insert node }

def dequeue? : ExtractM (Option SizedExpr) := do
  let { queue, .. } ← get
  let (next?, queue) := queue.extractMax
  modify ({ · with queue })
  return next?

def hasMin (eqc : Expr) : ExtractM Bool := do
  let { mins, .. } ← get
  return mins.contains ⟨eqc⟩

def getMin! (eqc : ExprPtr) : ExtractM Expr := do
  let { mins, .. } ← get
  return mins[eqc]!.expr

def setMin (eqc : Expr) (min : SizedExpr) : ExtractM Unit := do
  modify fun s => { s with mins := s.mins.insert ⟨eqc⟩ min }

/-- Returns the number of unique child e-classes. -/
def traverseAppChildEqcs (e : Expr) (k : Expr → ExtractM Unit) : ExtractM Nat := do
  let mut current := e
  let mut visited : HashSet ExprPtr := ∅
  repeat
    let (fn?, arg) := getFnArg? current
    -- We skip non-internalized expressions, as they (by definition) do not have e-nodes.
    if let some eqc ← getRoot? arg then
      if ⟨eqc⟩ ∉ visited then
        k eqc
        visited := visited.insert ⟨eqc⟩
    let some fn := fn? | break
    current := fn
  return visited.size
where
  getFnArg? (current : Expr) : (Option Expr) × Expr := Id.run do
    let .app fn arg := current | return (none, current)
    return (fn, arg)

nonrec def run (k : ExtractM α) : GoalM α := do
  Prod.fst <$> k.run ∅

end ExtractM

-- Note: Expects `target` to be internalized and hash-consed.
open ExtractM
partial def extractMinAST (target : Expr) : GoalM Expr := do
  run (init *> assign ⟨target⟩ *> construct target)
where
  init : ExtractM Unit := do
    for e in ← getExprs do
      if e.isApp then
        let numChildEqcs ← traverseAppChildEqcs e (addParent · e)
        -- If `numChildEqs = 0`, that means that all parts of the application `e` are non-
        -- internalized. In that case, we have to consider `e` to be a leaf node.
        if numChildEqcs = 0 then
          enqueue e.toSized
        else
          setPending e numChildEqcs
      else if e.isFalse then
        continue
      else
        enqueue e.toSized
  assign (target : ExprPtr) : ExtractM Unit := do
    repeat
      let some next ← dequeue? | return
      let eqc ← getRoot next.expr
      if ← hasMin eqc then continue
      setMin eqc next
      if ⟨eqc⟩ == target then return
      resolvePending eqc
  construct (eqcMem : Expr) : ExtractM Expr := do
    -- If the expression is not internalized, we return it as is.
    let some eqc ← getRoot? eqcMem | return eqcMem
    let node ← getMin! ⟨eqc⟩
    if node.isApp then
      node.traverseApp construct
    else
      return node

-- Note: Expects `target` to be internalized and hash-consed and `expr` to be hash-consed.
partial def extractExpr? (target expr : Expr) : GoalM (Option Expr) := do
  -- TODO: We probably need to check for grind gadgets as well.
  if expr.isApp then return ← extractApp? target expr
  match expr with
  | .mvar _  =>
    return target
  | .forallE n dom b i =>
    firstInEqc? target fun
      | .forallE _ dom' b' _ => do
        let some exDom ← extractExpr? dom' dom | return none
        let some exB ← extractExpr? b' b | return none
        return some <| .forallE n exDom exB i
      | _ => return none
  | .lam n dom b i =>
    firstInEqc? target fun
      | .lam _ dom' b' _ => do
        let some exDom ← extractExpr? dom' dom | return none
        let some exB ← extractExpr? b' b | return none
        return some <| .lam n exDom exB i
      | _ => return none
  | .lit _ | .const _ _ | .sort _ | .fvar _ | .bvar _ =>
    let isPresent ← anyInEqc? target (return isSameExpr · expr)
    if isPresent then return expr else return none
  | .app .. | .proj .. | .mdata .. | .letE .. =>
    panic! "reached invalid case in `extractExpr?`"
where
  -- Partial applications of functions are not necessarily internalized, so we need to obtain the
  -- entire application and extract for all arguments "at once".
  extractApp? (target expr : Expr) : GoalM (Option Expr) := do
    let fn := expr.getAppFn
    let args := expr.getAppArgs
    firstInEqc? target fun e => do
      unless e.isApp do return none
      let fn'   := e.getAppFn
      let args' := e.getAppArgs
      unless args.size = args'.size do return none
      let some exFn ← extractExpr? fn' fn | return none
      let mut exArgs := #[]
      for arg in args, arg' in args' do
        let some exArg ← extractExpr? arg' arg | return none
        exArgs := exArgs.push exArg
      return some <| mkAppN exFn exArgs

-- Note: This is expected to be run in the context of the failed grind goal, and with `target`
--       being internalized and hash-consed.
def extract? (target : Expr) (sketch : Sketch) : GoalM (Option Expr) := do
  match sketch with
  | .minAST =>
    extractMinAST target
  | .expr e =>
    let e ← shareCommon e
    extractExpr? target e
  | .or lhs rhs =>
    if let some ex ← extract? target lhs then
      return ex
    else
      extract? target rhs
  | .debug =>
    forEachEqcRoot fun root => do logInfo m!"{root.self}: {← getEqc root.self}"
    return none
  | _ =>
    throwError "`grind extract` does not currently support `[]ₛ` or nested (application) sketches"
