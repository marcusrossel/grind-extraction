import Extraction.Sketch
open Lean Meta Elab Term Tactic Grind

def extractEquivWithMinAST (mvarId : MVarId) (goal : Goal) : GrindM Expr := do
  let type ← mvarId.getType
  -- TODO
  return type

-- Corresponds to `Lean.Meta.Grind.main`.
def grindExtractMain (mvarId : MVarId) (params : Params) : MetaM Result := do profileitM Exception "grind" (← getOptions) do
  GrindM.runAtGoal mvarId params fun goal => do
    let failure? ← solve goal
    if failure?.isNone then
      mkResult params failure?
    else
      let min ← extractEquivWithMinAST mvarId goal
      throwError "failed, but found equivalent {min}"

-- Corresponds to `Lean.Elab.Tactic.grind`.
def grindExtract
    (mvarId : MVarId) (config : Grind.Config)
    (only : Bool) (ps : TSyntaxArray ``Parser.Tactic.grindParam)
    : TacticM Grind.Trace := do
  if debug.terminalTacticsAsSorry.get (← getOptions) then
    mvarId.admit
    return {}
  mvarId.withContext do
    let params ← mkGrindParams config only ps
    let type ← mvarId.getType
    let mvar' ← mkFreshExprSyntheticOpaqueMVar type
    let finalize (result : Grind.Result) : TacticM Grind.Trace := do
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
      return result.trace
    let result ← grindExtractMain mvar'.mvarId! params
    finalize result

-- Corresponds to `Lean.Elab.Tactic.evalGrindCore`.
def evalGrindExtractCore
    (ref : Syntax)
    (config : Grind.Config)
    (only : Option Syntax)
    (params? : Option (Syntax.TSepArray `Lean.Parser.Tactic.grindParam ","))
    : TacticM Grind.Trace := do
  let only := only.isSome
  let params := if let some params := params? then params.getElems else #[]
  if Grind.grind.warning.get (← getOptions) then
    logWarningAt ref "The `grind` tactic is new and its behavior may change in the future. This project has used `set_option grind.warning true` to discourage its use."
  withMainContext do
    let result ← grindExtract (← getMainGoal) config only params
    replaceMainGoal []
    return result

open Parser.Tactic in
syntax (name := Parser.Tactic.grindExtract)
    "grind" optConfig (&" only")? (" [" withoutPosition(grindParam,*) "]")? " extract" term : tactic

-- Corresponds to `Lean.Elab.Tactic.evalGrind`.
@[tactic Parser.Tactic.grindExtract] def evalGrindExtract : Tactic := fun stx => do
  match stx with
  | `(tactic| grind $config:optConfig $[only%$only]? $[[$params:grindParam,*]]? extract $sketch:term) =>
    let sketch ← elabSketch sketch
    let config ← elabGrindConfig config
    discard <| evalGrindExtractCore stx config only params
  | _ => throwUnsupportedSyntax
