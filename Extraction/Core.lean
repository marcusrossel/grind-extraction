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
    -- TODO: This might assign some mvars contained in the sketch that we do not want to assign.
    --       Also, we do not currently translate mvars from the outer context to grind's context. Is
    --       that ok?
    if ← (return !e.isFalse) <&&> isDefEq e expr then
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
  | _ =>
    throwError "`grind extract` currently only supports the `min_ast` and expression sketches"
