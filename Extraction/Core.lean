import Extraction.Lean
import Extraction.Sketch
open Lean Meta Elab Term Tactic Grind

namespace Lean.Meta.Grind.Extraction

-- TODO: The extraction mechanism so far is incorrect, as we are not considering equivalent
--       expressions for subterms. E.g. consider:
--
-- example (f g : Nat → Nat) (a b : Nat) (h : g a = b) : f (g a) = 0 := by
--   grind extract min_ast

structure SizedExpr where
  expr : Expr
  size : Nat

namespace SizedExpr

instance : Min SizedExpr where
  min e₁ e₂ := if e₁.size ≤ e₂.size then e₁ else e₂

def min? (e₁ : SizedExpr) (e₂? : Option SizedExpr) (threshold : Nat) : Option SizedExpr := Id.run do
  let mut m := e₁
  if let some e₂ := e₂? then m := min m e₂
  unless m.size ≤ threshold do return none
  return m

def app (fn arg : SizedExpr) : SizedExpr where
  expr := .app fn.expr arg.expr
  size := 1 + fn.size + arg.size

end SizedExpr

def _root_.Lean.Expr.toSized (e : Expr) : SizedExpr where
  expr := e
  size := e.sizeWithoutSharing

-- Note: Expects `target` to be internalized and hash-consed.
partial def extractMinAST (target : Expr) : GoalM Expr := do
  let target := target.toSized
  let some { expr, .. } ← go target target.size | return target.expr
  return expr
where
  go (target : SizedExpr) (threshold : Nat) : GoalM (Option SizedExpr) := do
    foldEqc target.expr target fun node best? => do
      let expr := node.self
      if expr.isFalse then return best?
      -- **TODO** How are children of other kinds of expressions to be handled? In particular, `.lam` and `.forallE`.
      unless expr.isApp do return expr.toSized.min? best? threshold
      let mut e := expr.getAppFn.toSized
      let mut threshold := threshold
      if let some best := best? then threshold := min threshold best.size
      threshold := threshold - e.size
      for arg in expr.getAppArgs do
        let arg := arg.toSized
        unless 0 < threshold do return best?
        -- **TODO** We only try to minimize arguments which are internalized.
        if ← alreadyInternalized arg.expr then
          let some minArg ← go arg threshold | return best?
          e := e.app minArg
          threshold := threshold - minArg.size
        else
          e := e.app arg
          threshold := threshold - arg.size
      return e

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
