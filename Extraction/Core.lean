import Extraction.Lean
import Extraction.Sketch
open Std Lean Meta Elab Term Tactic Grind

namespace Lean.Meta.Grind.Extraction

structure SizedExpr where
  expr : Expr
  size : Nat

namespace SizedExpr

instance : ToMessageData SizedExpr where
  toMessageData e := m!"[{e.size}] {e.expr}"

def app (fn arg : SizedExpr) : SizedExpr where
  expr := .app fn.expr arg.expr
  size := 1 + fn.size + arg.size

end SizedExpr

def _root_.Lean.Expr.toSized (e : Expr) : SizedExpr where
  expr := e
  size := e.sizeWithoutSharing

structure ExtractM.State where
  limit : Nat
  cache : HashMap ExprPtr SizedExpr

abbrev ExtractM := StateT ExtractM.State GoalM

namespace ExtractM

def limit : ExtractM Nat :=
  State.limit <$> get

def cache : ExtractM (HashMap ExprPtr SizedExpr) :=
  State.cache <$> get

def belowLimit (e : SizedExpr) : ExtractM Bool := do
  return e.size ≤ (← limit)

def setLimit (limit : Nat) : ExtractM Unit :=
  modify ({ · with limit })

def setCache (node : ExprPtr) (e : SizedExpr) : ExtractM Unit := do
  modify fun state => { state with cache := state.cache.insert node e }

def withCache (node : Expr) (k : ExtractM (Option SizedExpr)) : ExtractM (Option SizedExpr) := do
  let cache ← cache
  let node : ExprPtr := { expr := node }
  if let some e := cache[node]? then
    if ← belowLimit e then
      trace[grind.extract.minAST] "Cached: {e}"
      return e
    else
      trace[grind.extract.minAST] "Cached exceeds limit: {e}"
      return none
  else
    let some e ← k | return none
    setCache node e
    return e

/-- Runs a given computation, resetting the `← limit` afterwards. -/
def withResettingLimit (k : ExtractM α) : ExtractM α := do
  let limit ← limit
  let result ← k
  modify ({ · with limit })
  return result

/-- Runs a given computation with a given `limit`, resetting the `← limit` afterwards. -/
def withLimit (limit : Nat) (k : ExtractM α) : ExtractM α := do
  withResettingLimit do
    setLimit limit
    k

/--
Runs a given computation with the `← limit` reduced by a given amount `red`, and resets the
`← limit` afterwards. If the `← limit` is smaller than `red`, returns `none` without running `k`.
-/
def withReducingLimitBy (red : Nat) (k : ExtractM (Option SizedExpr)) : ExtractM (Option SizedExpr) := do
  let limit ← limit
  unless red ≤ limit do return none
  withLimit (limit - red) k

/-- Lifts `Grind.foldEqc` to `ExtractM` by propagating the `ExtractM.State` in the obvious way. -/
nonrec def foldEqc (e : Expr) (init : α) (f : ENode → α → ExtractM α) : ExtractM α := do
  let initState ← get
  let (result, finalState) ← foldEqc e (init, initState) fun node (a, state) => do
    let m := f node a
    m.run state
  set finalState
  return result

/--
Returns the smallest expression represented by any of the e-nodes in the e-class of `e`. The
extraction from an e-node is performed by `nodeMin?` where the input `Expr` is the e-node. We assume
that the expression returned by `nodeMin?` respects the `← limit` with which it was called. If no
expression with a size within the `← limit` can be found, `nodeMin?` should return `none`.
-/
def minInEqc (e : Expr) (nodeMin? : Expr → ExtractM (Option SizedExpr)) :
    ExtractM (Option SizedExpr) := do
  withResettingLimit do
    foldEqc e none fun node min? => do
      let some newMin ← nodeMin? node.self | return min?
      setLimit newMin.size
      return newMin

/--
Returns the result of a applying a function `f` to each part of an application. So, given `app` is
`fn arg₁ … argₙ`, returns `(f fn) (f arg₁) … (f argₙ)`. If any call to `f` returns `none`, the
function aborts and returns `none`. While traversing each component of the application, the
`← limit` is reduced by the size of the components processed so far. For example, when calling `f`
on `arg₃`, the `← limit` is set to `(← limit) - (f fn).size - (f arg₁).size - (f arg₂).size`.
-/
def traverseAppReducingLimit? (app : Expr) (f : Expr → ExtractM (Option SizedExpr)) :
    ExtractM (Option SizedExpr) := do
  let some fn ← f app.getAppFn | return none
  let mut e := fn
  for arg in app.getAppArgs do
    let some a ← withReducingLimitBy e.size do f arg | return none
    e := e.app a
  return e

end ExtractM

-- **TODO** Remove the fuel.
-- Note: Expects `target` to be internalized and hash-consed.
partial def extractMinAST (target : Expr) : GoalM Expr := do
  let state := { limit := target.sizeWithoutSharing, cache := ∅ }
  let (e?, _) ← go target |>.run state
  let some e := e? | return target
  return e.expr
where
  go (target : Expr) : ExtractM (Option SizedExpr) := open ExtractM in do
    withTraceNode `grind.extract.minAST (fun _ => return m!"Extracting from {target}") do
      trace[grind.extract.minAST] "Limit: {← limit}"
      let min? ← minInEqc target fun node => do
        withTraceNode `grind.extract.minAST (fun _ => return m!"E-Node {node}") do
          withCache node do
            if node.isFalse then return none
            -- **TODO** How are children of other kinds of expressions to be handled? In particular, `.lam` and `.forallE`.
            unless node.isApp do
              let node := node.toSized
              if ← belowLimit node then return node else return none
            traverseAppReducingLimit? node fun e => do
              -- **TODO** We only try to minimize arguments which are internalized.
              unless ← alreadyInternalized e do
                trace[grind.extract.minAST] "Non-Internalized Arg: {e}"
                return e.toSized
              go e
      if let some min := min? then trace[grind.extract.minAST] "Minimal: {min}"
      return min?

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
