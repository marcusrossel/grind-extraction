import Extraction.AStar
import Extraction.ExprSize
import Extraction.Lean
import Extraction.Sketch

namespace Lean.Meta.Grind.Extraction

-- Note: Expects `target` to be internalized and hash-consed.
partial def extractMinAST (target : Expr) : GoalM Expr := do
  AStar.extract target fun node childCosts? =>
    -- **TODO** The `fixedAppSize?` breaks superiority which might be a problem.
    if let some fixed := fixedAppSize? node then
      fixed
    else if let some childCosts := childCosts? then
      if childCosts.isEmpty then
        exprSize node -- Exact cost when `node` is a leaf.
      else
        childCosts.sum -- Exact cost when `node` is an app.
    else if node.isApp then
      node.getAppNumArgs -- Lower bound cost when `node` is an app.
      -- Note, this is one less than the number of children of `node`. If we chose exactly the
      -- number of children as the cost, then when a child of `node` inherits this path cost, its
      -- merit might *exceed* the actual cost. For example, if we gave `f a b c d` a path cost of
      -- `5`, then its child `a` will have a merit of `6` or more which might exceed the cost of
      -- `f a b c d`.
    else
      exprSize node -- Lower bound cost when `node` is a leaf.

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
