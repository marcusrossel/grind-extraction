import Extraction.Lean
import Extraction.Sketch
import Batteries
open Std Lean Meta Elab Term Tactic Grind
open Batteries (BinaryHeap)

namespace Lean.Meta.Grind.Extraction

/--
Special constants which force applications to have a fixed cost. For example, we want the
application `@OfNat.ofNat α n inst` to have a fixed cost of `1` instead of accounting for the sizes
of `α`, `n` and `inst`.
-/
def fixedAppSize? (e : Expr) : Option Nat :=
  match_expr e with
  | OfNat.ofNat _ _ _ => some 1
  | _                 => none

/--
We use this size function instead of `Expr.sizeWithoutSharing` to more closely match the size which
is computed (incrementally) by `extractMinAST.assign`. This implementation will likely change in the
future.
-/
def exprSize (e : Expr) : Nat :=
  if let some fixed := fixedAppSize? e then
    fixed
  else
    match e with
    | .app fn arg               => exprSize fn + exprSize arg
    | .lam _ dom body _         => exprSize dom + exprSize body
    | .forallE _ dom body _     => exprSize dom + exprSize body
    | .letE _ type value body _ => exprSize type + exprSize value + exprSize body
    | .mdata _ e                => exprSize e
    | .proj _ _ s               => exprSize s + 1
    | _                         => 1

structure SizedExpr where
  expr : Expr
  size : Nat
  deriving Inhabited

instance SizedExpr.instToMessageData : ToMessageData SizedExpr where
  toMessageData e := m!"[{e.size}] {e.expr}"

instance : Coe SizedExpr MessageData where
  coe := toMessageData

def _root_.Lean.Expr.toSized (e : Expr) : SizedExpr where
  expr := e
  size := exprSize e

abbrev ExtractM.Queue := BinaryHeap SizedExpr (·.size > ·.size)

structure ExtractM.State where
  /-- Records the minimal e-node for each e-class. Note that we expect the given `ExprPtr` to be the
      `root` of the e-class. The size associated with each e-node is the the size which its minimal
      representation *will* have when/if constructed. -/
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
  /-- The priority queue used to decide in which order to visit e-nodes during the main loop of
      bottom-up extraction. -/
  queue : Queue
  /-- Maps e-classes to their minimal representative *expression*. This is used to make construction
      of the minimal expression more efficient in `extractMinAST.construct`. -/
  cache : HashMap ExprPtr Expr

instance ExtractM.State.instEmptyCollection : EmptyCollection State where
  emptyCollection := { mins := ∅, parents := ∅, pending := ∅, queue := ∅, cache := ∅ }

abbrev ExtractM := StateT ExtractM.State GoalM

namespace ExtractM

def traceExtract (msg : Thunk MessageData) : ExtractM Unit := do
  trace[grind.extract.minAST] msg.get

def withTraceExtractNode (msg : Thunk MessageData) (k : ExtractM α) : ExtractM α :=
  withTraceNode `grind.extract.minAST (fun _ => return msg.get) k

def traceMins : ExtractM Unit := do
  withTraceExtractNode "Assigned" do
    let { mins, .. } ← get
    if mins.isEmpty then
      traceExtract "∅"
    else
      let mut trivials := #[]
      let mut assignments := #[]
      for (eqc, min) in mins do
        let eqc ← getEqc eqc.expr
        if eqc.length = 1 then
          trivials := trivials.push min
        else
          assignments := assignments.push (eqc, min)
      for (eqc, min) in assignments do
        traceExtract m!"{eqc} ↦ {min}"
      unless trivials.isEmpty do
        withTraceExtractNode "Trivial" do
          for node in trivials do
            traceExtract node

def tracePending : ExtractM Unit := do
  withTraceExtractNode "Pending" do
    let { pending, .. } ← get
    if pending.isEmpty then
      traceExtract "∅"
    else
      for (node, num) in pending do
        traceExtract m!"{node.expr} ↦ {num}"

def traceParents : ExtractM Unit := do
  withTraceExtractNode "Parents" do
    let { parents, .. } ← get
    if parents.isEmpty then
      traceExtract "∅"
    else
      for (eqc, parents) in parents do
        let eqc ← getEqc eqc.expr
        withTraceExtractNode m!"Of {eqc}" do
          for parent in parents do
            traceExtract parent.expr

def traceQueue : ExtractM Unit := do
  withTraceExtractNode "Queue" do
    let { queue, .. } ← get
    let queue := queue.arr
    if queue.isEmpty then
      traceExtract "∅"
    else
      let queue := queue -- **TODO** sort the queue.
      for node in queue do
        traceExtract node

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
def updateParents (eqc : Expr) : ExtractM Unit := do
  let eqc : ExprPtr := ⟨eqc⟩
  let s ← get
  let some eqcParents := s.parents[eqc]? | return
  withTraceExtractNode "Updating Parent E-Nodes" do
    let mut pending := s.pending
    let mut queue := s.queue
    for parent in eqcParents do
      let some (num + 1) := pending[parent]? | continue
      pending := pending.insert parent num
      traceExtract m!"{parent.expr} ↦ {num} pending"
      if num = 0 then
        -- This is not the size of `parent.expr`, but rather the size which its minimal
        -- representation *will* have when/if constructed.
        let size ← nodeSize! parent
        traceExtract m!"Enqueuing {parent.expr}"
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

def getMin! (eqc : ExprPtr) : ExtractM SizedExpr := do
  let { mins, .. } ← get
  return mins[eqc]!

def setMin (eqc : Expr) (min : SizedExpr) : ExtractM Unit := do
  modify fun s => { s with mins := s.mins.insert ⟨eqc⟩ min }

/-- Returns the unique child e-classes. -/
def traverseAppChildEqcs (e : Expr) (k : Expr → ExtractM Unit) : ExtractM (HashSet ExprPtr) := do
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
  return visited
where
  getFnArg? (current : Expr) : (Option Expr) × Expr := Id.run do
    let .app fn arg := current | return (none, current)
    return (fn, arg)

def withCache (eqc : ExprPtr) (k : ExtractM Expr) : ExtractM Expr := do
  let { cache, .. } ← get
  if let some e := cache[eqc]? then
    return e
  else
    let e ← k
    modify ({ · with cache := cache.insert eqc e })
    return e

nonrec def run (k : ExtractM α) : GoalM α := do
  Prod.fst <$> k.run ∅

end ExtractM

-- Note: Expects `target` to be internalized and hash-consed.
open ExtractM
partial def extractMinAST (target : Expr) : GoalM Expr := do
  run do
    withTraceExtractNode "Initializing" do init
    withTraceExtractNode "Assigning"    do assign ⟨target⟩
    withTraceExtractNode "Constructing" do construct target
where
  init : ExtractM Unit := do
    -- **TODO** Only traverse the e-nodes reachable from `target`.
    for e in ← getExprs do
      withTraceExtractNode e do
        if e.isApp then
          -- Fixed cost applications are considered to be leaves as we do not care about their child
          -- nodes. We need to take special care not to look at their child e-classes during
          -- `construct`, as the `mins` may not contain an assignment for these.
          if let some size := fixedAppSize? e then
            traceExtract "Enqueuing fixed cost application leaf"
            enqueue { expr := e, size }
          else
            let childEqcs ← traverseAppChildEqcs e (addParent · e)
            -- If `numChildEqs = 0`, that means that all parts of the application `e` are non-
            -- internalized. In that case, we have to consider `e` to be a leaf node.
            if childEqcs.isEmpty then
              traceExtract "Enqueuing application leaf with no internalized children"
              enqueue e.toSized
            else
              traceExtract m!"Pending: {childEqcs.toList.map (·.expr)}"
              setPending e childEqcs.size
        else if !e.isFalse then
          traceExtract "Enqueuing basic leaf"
          enqueue e.toSized
        traceQueue
        tracePending
        traceParents
  assign (target : ExprPtr) : ExtractM Unit := do
    while let some next ← dequeue? do
      withTraceExtractNode next do
        traceQueue
        traceMins
        let eqc ← getRoot next.expr
        if ← hasMin eqc then
          traceExtract m!"E-Class of {inlineExpr next.expr}is already assigned"
        else
          traceExtract m!"Setting{inlineExpr next.expr}as minimum of its e-class"
          setMin eqc next
          if ⟨eqc⟩ == target then
            traceExtract m!"E-class of target{inlineExpr target.expr}is assigned"
            return
          else
            updateParents eqc
  construct (eqcMem : Expr) : ExtractM Expr := do
    -- If the expression is not internalized, we return it as is.
    let some eqc ← getRoot? eqcMem | return eqcMem
    withCache ⟨eqc⟩ do
      let { expr := node, .. } ← getMin! ⟨eqc⟩
      -- Applications with a fixed cost are treated as leaves. We have to respect this here not only
      -- as an optimization, but as `mins` may not contain assignments for their child e-classes.
      if node.isApp && (fixedAppSize? node).isNone then
        let e ← node.traverseApp construct
        traceExtract e
        return e
      else
        traceExtract node
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
    let some ex ← extractExpr? target e | return none
    return ex
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
