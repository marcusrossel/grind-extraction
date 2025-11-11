import Extraction.Lean
import Extraction.Sketch
open Lean Meta Elab Term Tactic Grind

namespace Lean.Meta.Grind.Extraction

-- Note: Expects `target` to be internalized.
def extractMinAST (target : Expr) : GoalM Expr := do
  foldEqc target target fun node min => do
    let expr := node.self
    if expr.isFalse then return min
    if expr.sizeWithoutSharing < min.sizeWithoutSharing then return expr else return min

-- Note: Expects `target` and `e` to be internalized.
def extractExpr? (target expr : Expr) : GoalM (Option Expr) := do
  unless expr.hasMVar do
    if ← isEqv target expr then
      return expr
    else
      return none
  firstInEqc? target fun e => do
    -- TODO: We might be careful to reset any assignments performed by isDefEq, as not to hinder the
    --       possibility of later assignments of sketches' holes.
    if ← (return !e.isFalse) <&&> isDefEq expr e then
      return e
    else
      return none

-- Note: This is expected to be run in the context of the failed grind goal, and with `target`
--       being internalized.
def extract? (target : Expr) : Sketch → GoalM (Option Expr)
  | .minAST => do
    extractMinAST target
  | .expr e => do
    let e ← shareCommon e
    extractExpr? target e
  | .or lhs rhs => do
    if let some ex ← extract? target lhs then
      return ex
    else
      extract? target rhs
  | _ =>
    throwError "`grind extract` does not currently support `[]ₛ` or nested (application) sketches"
