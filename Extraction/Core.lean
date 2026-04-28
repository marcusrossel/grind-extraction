import Extraction.Lean
import Extraction.Sketch
open Lean Meta Elab Term Tactic Grind

namespace Lean.Meta.Grind.Extraction

-- TODO: The extraction mechanism so far is incorrect, as we are not considering equivalent
--       expressions for subterms. E.g. consider:
--
-- example (f g : Nat → Nat) (a b : Nat) (h : g a = b) : f (g a) = 0 := by
--   grind extract min_ast

-- Note: Expects `target` to be internalized and hash-consed.
def extractMinAST (target : Expr) : GoalM Expr := do
  foldEqc target target fun node min => do
    let expr := node.self
    if expr.isFalse then return min
    if expr.sizeWithoutSharing < min.sizeWithoutSharing then return expr else return min

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
