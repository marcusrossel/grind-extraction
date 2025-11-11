import Extraction.Core
import Extraction.Lean
open Lean Meta Elab Parser Tactic Grind Extraction

/- This file defines the uninteresting part of the `grind extract` elaborator, which mainly consists
   of slight modifications to high-level functions of (vanilla) grind's elaborator.
-/

namespace Lean.Meta.Grind.Extraction

-- Note: The replacement of fvars may be sketchy, as while `grind` sets `preserveOrder := true` when
--       calling `revertAll`, I'm not sure if there are other aspects which may affect the order of
--       fvars in `grind`'s local context. For example, does `intros` preserve the order?
def exprToGrind (oldFVars newFVars : Array Expr) (e : Expr) : MetaM Expr := do
  let e := e.replaceFVars oldFVars (newFVars.take oldFVars.size)
  let e ← Grind.unfoldReducible e
  Core.betaReduce e

def Sketch.toGrind (oldFVars newFVars : Array Expr) (sketch : Sketch) : MetaM Sketch := do
  match sketch with
  | expr e          => return expr (← exprToGrind oldFVars newFVars e)
  | app fn arg      => return app (← fn.toGrind oldFVars newFVars) (← arg.toGrind oldFVars newFVars)
  | contains sketch => return contains (← sketch.toGrind oldFVars newFVars)
  | or lhs rhs      => return or (← lhs.toGrind oldFVars newFVars) (← rhs.toGrind oldFVars newFVars)
  | minAST          => return minAST

-- TODO: We just translate the fvars back naively for now, as our goal is first to test different
--       kinds of extraction, so it's ok if this fails sometimes.
def exprFromGrind (oldFVars newFVars : Array Expr) (e : Expr) : Expr :=
  e.replaceFVars (newFVars.take oldFVars.size) oldFVars

def onFailure (target : MVarId) (sketch : Sketch) (oldFVars : Array Expr) :
    GoalM (Option Expr) := do
  let newFVars ← getLocalHyps
  let target ← target.getType
  let target ← exprToGrind oldFVars newFVars target
  let target ← shareCommon target
  let sketch ← sketch.toGrind oldFVars newFVars
  let some ex ← extract? target sketch | return none
  return exprFromGrind oldFVars newFVars ex

protected inductive Result where
  /-- `grind` succeeded. -/
  | grind (result : Grind.Result)
  /-- `grind` failed and extraction succeeded. -/
  | extracted (ex : Expr)
  /-- Neither `grind`, nor extraction succeeded. -/
  | failure (result : Grind.Result)

-- Corresponds to `Lean.Meta.Grind.main`.
protected def main (target : MVarId) (params : Params) (sketch : Sketch) :
    MetaM Extraction.Result := do
  profileitM Exception "grind" (← getOptions) do
    let oldFVars ← getLocalHyps
    GrindM.runAtGoal target params fun goal => do
      let failure? ← solve goal
      let some failedGoal := failure? | return .grind (← mkResult params failure?)
      let (ex?, _) ← GoalM.run failedGoal do onFailure target sketch oldFVars
      let some ex := ex? | return .failure (← mkResult params failure?)
      return .extracted ex

end Lean.Meta.Grind.Extraction

namespace Lean.Elab.Tactic.Extraction

-- Corresponds to `Lean.Elab.Tactic.grind`.
protected def grind
    (mvarId : MVarId) (config : Grind.Config) (only : Bool) (ps : TSyntaxArray ``grindParam)
    (sketch : Sketch) : TacticM (Option Expr) := do
  if debug.terminalTacticsAsSorry.get (← getOptions) then
    mvarId.admit
    return none
  mvarId.withContext do
    let params ← mkGrindParams config only ps
    let type ← mvarId.getType
    let mvar' ← mkFreshExprSyntheticOpaqueMVar type
    let finalize (result : Grind.Result) : TacticM Unit := do
      if result.hasFailed then
        throwError "`grind extract` failed\n{← result.toMessageData}"
      trace[grind.debug.proof] "{← instantiateMVars mvar'}"
      -- `grind` proofs are often big, if `abstractProof` is true, we create an auxiliary theorem.
      let e ← if !config.abstractProof then
        instantiateMVarsProfiling mvar'
      else if (← isProp type) then
        mkAuxTheorem type (← instantiateMVarsProfiling mvar') (zetaDelta := true)
      else
        let auxName ← Term.mkAuxName `grind
        mkAuxDefinition auxName type (← instantiateMVarsProfiling mvar') (zetaDelta := true)
      mvarId.assign e
    let result ← Extraction.main mvar'.mvarId! params sketch
    match result with
    | .grind result | .failure result =>
      finalize result
      return none
    | .extracted ex =>
      return ex

declare_syntax_cat grindExtractPrefix
syntax "grind" optConfig (&" only")? (" [" withoutPosition(grindParam,*) "]")? : grindExtractPrefix

declare_syntax_cat grindExtractHead
syntax grindExtractPrefix " extract" : grindExtractHead

-- TODO: How does one properly turn `Syntax` into `MessageData`?
def mkGrindSuffices (ex : Expr) (sketch : Syntax) :
    TSyntax `grindExtractHead → TacticM TryThis.Suggestion
  | `(grindExtractHead| $pre:grindExtractPrefix extract) => do
    let msg := m!"suffices «{sketch.prettyPrint}» : {← ppExpr ex} by {pre.raw.prettyPrint}"
    msg.toString
  | _ => unreachable!

-- Corresponds to `Lean.Elab.Tactic.evalGrindCore`.
protected def evalGrindCore
    (head : TSyntax `grindExtractHead) (sketch : Term) (config : Grind.Config)
    (only : Option Syntax) (params? : Option (Syntax.TSepArray ``grindParam ",")) :
    TacticM Unit := do
  let only := only.isSome
  let params := if let some params := params? then params.getElems else #[]
  if Grind.grind.warning.get (← getOptions) then
    logWarningAt head "The `grind` tactic is new and its behavior may change in the future. This project has used `set_option grind.warning true` to discourage its use."
  withMainContext do
    let sk ← Sketch.elabSketch sketch
    let ex? ← Extraction.grind (← getMainGoal) config only params sk
    let some ex := ex? | replaceMainGoal []
    let suggestion ← mkGrindSuffices ex sketch head
    Tactic.TryThis.addSuggestion head suggestion (origSpan? := ← getRef)

syntax (name := Parser.Tactic.grindExtract) grindExtractHead term : tactic

-- Corresponds to `Lean.Elab.Tactic.evalGrind`.
@[tactic Parser.Tactic.grindExtract] def evalGrind : Tactic
  | `(tactic| $head:grindExtractHead $sketch:term) => do
    match head with
    | `(grindExtractHead| grind $config:optConfig $[only%$only]? $[[$params:grindParam,*]]? extract) =>
      let config ← elabGrindConfig config
      discard <| Extraction.evalGrindCore head sketch config only params
    | _ => throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax
