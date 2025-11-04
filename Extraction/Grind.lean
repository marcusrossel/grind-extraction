import Extraction.Core
import Extraction.Lean
open Lean Elab Parser Tactic

/- This file defines the uninteresting part of the `grind extract` elaborator, which mainly consists
   of slight modifications to high-level functions of (vanilla) grind's elaborator.
-/

namespace Lean.Meta.Grind.Extraction

protected inductive Result where
  | extracted (ex : Extracted)
  | grind (result : Grind.Result)

-- Note: The replacement of fvars may be sketchy, as while `grind` sets `preserveOrder := true` when
--       calling `revertAll`, I'm not sure if there are other aspects which may affect the order of
--       fvars in `grind`'s local context. For example, does `intros` preserve the order?
def exprToGrind (oldFVars newFVars : Array Expr) (e : Expr) : MetaM Expr := do
  let e := e.replaceFVars oldFVars (newFVars.take oldFVars.size)
  let e ← Grind.unfoldReducible e
  Core.betaReduce e

-- TODO: We just translate the fvars back naively for now, as our goal is first to test different
--       kinds of extraction, so it's ok if this fails sometimes.
def exprFromGrind (oldFVars newFVars : Array Expr) (e : Expr) : Expr :=
  e.replaceFVars (newFVars.take oldFVars.size) oldFVars

def Extracted.fromGrind (oldFVars newFVars : Array Expr) (ex : Extracted) : Extracted where
  result     := exprFromGrind oldFVars newFVars ex.result
  eqHEqProof := exprFromGrind oldFVars newFVars ex.eqHEqProof

-- Corresponds to `Lean.Meta.Grind.main`.
protected def main
    (target : MVarId) (params : Params) (sketch : Sketch) : MetaM Extraction.Result := do
  profileitM Exception "grind" (← getOptions) do
    let oldFVars ← getLocalHyps
    GrindM.runAtGoal target params fun goal => do
      let failure? ← solve goal
      if let some failedGoal := failure? then
        let (extracted?, _) ← GoalM.run failedGoal do
          let newFVars ← getLocalHyps
          let target ← target.getType
          let target ← exprToGrind oldFVars newFVars target
          let some ex ← extract target sketch | return none
          return some <| ex.fromGrind oldFVars newFVars
        if let some extracted := extracted? then
          return .extracted extracted
      return .grind (← mkResult params failure?)

-- Corresponds to `Lean.Elab.Tactic.grind`.
protected def grind
    (mvarId : MVarId) (config : Grind.Config) (only : Bool) (ps : TSyntaxArray ``grindParam)
    (sketch : Sketch) : TacticM (Option Extracted) := do
  if debug.terminalTacticsAsSorry.get (← getOptions) then
    mvarId.admit
    return none
  mvarId.withContext do
    let params ← mkGrindParams config only ps
    let type ← mvarId.getType
    let mvar' ← mkFreshExprSyntheticOpaqueMVar type
    let finalize (result : Grind.Result) : TacticM Unit := do
      if result.hasFailed then
        throwError "`grind` failed\n{← result.toMessageData}"
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
    | .extracted ex =>
      return ex
    | .grind result =>
      finalize result
      return none

-- Corresponds to `Lean.Elab.Tactic.evalGrindCore`.
protected def evalGrindCore
    (ref : Syntax) (config : Grind.Config) (only : Option Syntax)
    (params? : Option (Syntax.TSepArray ``grindParam ",")) (sketch : Sketch) : TacticM Unit := do
  let only := only.isSome
  let params := if let some params := params? then params.getElems else #[]
  if Grind.grind.warning.get (← getOptions) then
    logWarningAt ref "The `grind` tactic is new and its behavior may change in the future. This project has used `set_option grind.warning true` to discourage its use."
  withMainContext do
    let ex? ← Extraction.grind (← getMainGoal) config only params sketch
    let some ex := ex? | replaceMainGoal []
    let goal ← getMainGoal
    let tag ← goal.getTag
    let newGoal ← mkFreshExprSyntheticOpaqueMVar ex.result tag
    let proof ← mkEqHEqMP ex.eqHEqProof newGoal
    goal.assign proof
    replaceMainGoal [newGoal.mvarId!]

syntax (name := Parser.Tactic.grindExtract)
  "grind" optConfig (&" only")? (" [" withoutPosition(grindParam,*) "]")? " extract" term : tactic

-- Corresponds to `Lean.Elab.Tactic.evalGrind`.
@[tactic Parser.Tactic.grindExtract] def evalGrindExtract : Tactic := fun stx => do
  match stx with
  | `(tactic| grind $config:optConfig $[only%$only]? $[[$params:grindParam,*]]? extract $sketch:term) =>
    let config ← elabGrindConfig config
    let sketch ← elabSketch sketch
    discard <| Extraction.evalGrindCore stx config only params sketch
  | _ => throwUnsupportedSyntax
