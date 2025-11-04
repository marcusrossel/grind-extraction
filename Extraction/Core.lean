import Extraction.Sketch
open Lean Meta Elab Term Tactic Grind

namespace Lean.Meta.Grind.Extraction

-- Note: Expects `target` to be internalized.
def extractMinAST (target : Expr) : GoalM Expr := do
  let min ← foldEqc target target fun node min => do
    let expr := node.self
    if expr.isFalse then return min
    if expr.sizeWithoutSharing < min.sizeWithoutSharing then return expr else return min
  return min

-- Note: Expects `target` and `e` to be internalized.
def extractExpr? (target e : Expr) : GoalM (Option Expr) := do
  -- TODO: Support mvars.
  unless ← isEqv target e do return none
  return e

def extractMain? (target : Expr) : Sketch → GoalM (Option Expr)
  | .minAST => do
    let min ← extractMinAST target
    return min
  | .expr e => do
    let e ← shareCommon e
    extractExpr? target e
  | _ =>
    throwError "`grind extract` currently only supports the `min_ast` and expression sketches"

structure Extracted where
  /-- The result of extraction: the extracted term, equivalent to the proof goal. -/
  result     : Expr
  /-- Proves `result = target`/`result ≍ target`. -/
  eqHEqProof : Expr

-- Note: This is expected to be run in the context of the failed grind goal, and with `target`
--       being internalized.
def extract? (target : Expr) (sketch : Sketch) : GoalM (Option Extracted) := do
  let some result ← extractMain? target sketch | return none
  let eqHEqProof ← mkEqHEqProof result target
  return some { result, eqHEqProof }
