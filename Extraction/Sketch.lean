import Lean
open Lean Meta Elab Term Command

namespace Lean

inductive Meta.Grind.Extraction.Sketch where
  -- Holes are represented as `.expr (.mvar _)`.
  | expr (e : Expr)
  | app (fn arg : Sketch)
  | contains (sketch : Sketch)
  | or (lhs rhs : Sketch)
  | minAST

namespace KVMap

private def sketchContainsKey := `sketchContainsKey
private def sketchOrLhsKey    := `sketchOrLhsKey
private def sketchOrRhsKey    := `sketchOrRhsKey
private def sketchMinASTKey   := `sketchMinASTKey

def mkContainsSketch (t : Term) : KVMap :=
  { : KVMap }.setSyntax sketchContainsKey t

def mkOrSketch (lhs rhs : Term) : KVMap :=
  { : KVMap } |>.setSyntax sketchOrLhsKey lhs |>.setSyntax sketchOrRhsKey rhs

def mkMinASTSketch (ref : Syntax) : KVMap :=
  { : KVMap } |>.setSyntax sketchMinASTKey ref

def containsSketchKey (kv : KVMap) : Bool :=
  kv.contains sketchContainsKey
  || kv.contains sketchOrLhsKey
  || kv.contains sketchOrRhsKey

end KVMap

def Expr.containsSketchGadget : Expr → Bool
  | .mdata data e =>
    data.containsSketchKey || e.containsSketchGadget
  | .app e₁ e₂ | .lam _ e₁ e₂ _ | .forallE _ e₁ e₂ _ =>
    e₁.containsSketchGadget || e₂.containsSketchGadget
  | .letE _ e₁ e₂ e₃ _ =>
    e₁.containsSketchGadget || e₂.containsSketchGadget || e₃.containsSketchGadget
  | _ =>
    false

def MData.getContainsSketch? (data : MData) : Option Syntax := do
  let some (.ofSyntax cont) := data.find KVMap.sketchContainsKey | none
  cont

def MData.getOrSketches? (data : MData) : Option (Syntax × Syntax) := do
  let some (.ofSyntax orLhs) := data.find KVMap.sketchOrLhsKey | none
  let some (.ofSyntax orRhs) := data.find KVMap.sketchOrRhsKey | none
  (orLhs, orRhs)

def MData.getMinASTSketch? (data : MData) : Option Syntax := do
  let some (.ofSyntax ref) := data.find KVMap.sketchMinASTKey | none
  ref

namespace Meta.Grind.Extraction.Sketch

syntax "[" term "]ₛ" : term        -- Sketch.contains
syntax:min term " |ₛ " term : term -- Sketch.or
syntax "min_ast" : term            -- Sketch.minAST

elab_rules : term
  | `([$t:term]ₛ)             => return .mdata (KVMap.mkContainsSketch t) (← mkFreshExprMVar none)
  | `($lhs:term |ₛ $rhs:term) => return .mdata (KVMap.mkOrSketch lhs rhs) (← mkFreshExprMVar none)
  | `(min_ast%$ref)           => return .mdata (KVMap.mkMinASTSketch ref) (← mkFreshExprMVar none)

-- TODO: We should probably normalize things with `grind`'s normalization procedure, if we want to
--       hope to find expressions in the e-graph. For example, I think `grind` ζ-reduces.
partial def elabSketch (stx : TSyntax `term) : TermElabM Sketch := do
  let e ← withoutErrToSorry do elabTerm stx none
  -- We instantiate mvars, as otherwise terms like `(1 : Nat)` do not resolve the type variables of
  -- `OfNat.ofNat` to `Nat`.
  let e ← instantiateMVars e
  let sketch ← go e
  return sketch
where
  go : Expr → TermElabM Sketch
    | .mdata data e => do
      if let some cont := data.getContainsSketch? then
        let s ← elabSketch ⟨cont⟩
        return .contains s
      if let some (orLhs, orRhs) := data.getOrSketches? then
        let lhs ← elabSketch ⟨orLhs⟩
        let rhs ← elabSketch ⟨orRhs⟩
        return .or lhs rhs
      if let some _ := data.getMinASTSketch? then
        return .minAST
      return .expr e
    | .app fn arg =>
      -- This check normalizes our sketch representation, such that we don't introduce unnecessary
      -- `Sketch.app`s, where `Expr.app`s would have sufficed.
      if fn.containsSketchGadget || arg.containsSketchGadget then
        return .app (← go fn) (← go arg)
      else
        return .expr (.app fn arg)
    | e@(.lam ..) | e@(.forallE ..) | e@(.letE ..) =>
      if e.containsSketchGadget then
        throwErrorAt stx "sketches may not appear under binders"
      else
        return .expr e
    | e =>
      return .expr e

-- TODO: Improve this. E.g. how does pretty printing expressions ensure that applications contain
--       parentheses when necessary, and only when necessary.
--       Also use `MessageData` so you get info on hover.
def format : Sketch → Format
  | expr e               => Std.ToFormat.format e
  | app fn arg@(.app ..)
  | app fn arg@(.or ..)  => format fn ++ " " ++ "(" ++ format arg ++ ")"
  | app fn arg           => format fn ++ " " ++ format arg
  | contains sketch      => "[" ++ format sketch ++ "]ₛ"
  | or sketch₁ sketch₂   => format sketch₁ ++ " |ₛ " ++ format sketch₂
  | minAST               => "min_ast"

instance : Std.ToFormat Sketch where
  format := Sketch.format

elab "#show_sketch " sketch:term : command => do
  let sketch ← liftTermElabM do elabSketch sketch
  logInfo <| format sketch
