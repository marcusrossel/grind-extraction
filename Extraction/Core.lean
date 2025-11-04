import Extraction.Sketch
open Lean Meta Elab Term Tactic Grind

namespace Lean.Meta.Grind.Extraction

def extractMinAST (target : Expr) : GoalM (Expr × Expr) := do
  let target ← shareCommon target
  let min ← foldEqc target target fun node min => do
    let expr := node.self
    if expr.isFalse then return min
    if expr.sizeWithoutSharing < min.sizeWithoutSharing then return expr else return min
  return (target, min)

structure Extracted where
  /-- The result of extraction: the extracted term, equivalent to the proof goal. -/
  result     : Expr
  /-- Proves `result = target`/`result ≍ target`. -/
  eqHEqProof : Expr

def extract (target : Expr) (sketch : Sketch) : GoalM (Option Extracted) := do
  let .minAST := sketch | throwError "`grind extract` currently only supports the `min_ast` sketch"
  let (internalizedTarget, result) ← extractMinAST target
  let eqHEqProof ← mkEqHEqProof result internalizedTarget
  return some { result, eqHEqProof }
