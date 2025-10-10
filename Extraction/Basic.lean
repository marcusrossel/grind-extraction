import Extraction.Sketch
open Lean Meta Elab Term Tactic Grind

-- CURRENT ISSUE: The `mvarId` and `goal.mvarId` have different mvars, and this seems to affect
--              even local variables. So for example for local `f : Nat → Nat`, the term `f 1`
--              will have a different fvar id for `f` in the two contexts. This might be a
--              result of `grind` reverting (and presumably reintroducing) everything before it
--              gets started (`Grind.initCore`).
def extractEquivWithMinAST (mvarId : MVarId) (goal : Goal) : GrindM Expr := do
  let type ← shareCommon (← mvarId.getType)
  let mut min     := type
  let mut current := type
  while true do
    let some node := goal.getENode? current | break
    if node.isRoot then break
    current := node.next
    if current.isFalse then continue
    if current.sizeWithoutSharing < min.sizeWithoutSharing then min := current
  return min

def extract (mvarId : MVarId) (goal : Goal) (sketch : Sketch) : GrindM (Option Expr) := do
  let .min := sketch | throwError "`grind extract` currently only supports the `min_ast` sketch"
  extractEquivWithMinAST mvarId goal

inductive ExtractResult where
  | extracted (e : Expr)
  | grind (result : Result)

-- Corresponds to `Lean.Meta.Grind.main`.
def grindExtractMain (mvarId : MVarId) (params : Params) (sketch : Sketch) : MetaM ExtractResult := do
  profileitM Exception "grind" (← getOptions) do
    GrindM.runAtGoal mvarId params fun goal => do
      let failure? ← solve goal
      if let some failedGoal := failure? then
        if let some extracted ← extract mvarId failedGoal sketch then
          return .extracted extracted
      return .grind (← mkResult params failure?)

-- Corresponds to `Lean.Elab.Tactic.grind`.
def grindExtract
    (mvarId : MVarId) (config : Grind.Config)
    (only : Bool) (ps : TSyntaxArray ``Parser.Tactic.grindParam) (sketch : Sketch)
    : TacticM (Option Expr) := do
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
    let result ← grindExtractMain mvar'.mvarId! params sketch
    match result with
    | .extracted e =>
      return e
    | .grind result =>
      finalize result
      return none

-- Corresponds to `Lean.Elab.Tactic.evalGrindCore`.
def evalGrindExtractCore
    (ref : Syntax)
    (config : Grind.Config)
    (only : Option Syntax)
    (params? : Option (Syntax.TSepArray `Lean.Parser.Tactic.grindParam ","))
    (sketch : Sketch)
    : TacticM Unit := do
  let only := only.isSome
  let params := if let some params := params? then params.getElems else #[]
  if Grind.grind.warning.get (← getOptions) then
    logWarningAt ref "The `grind` tactic is new and its behavior may change in the future. This project has used `set_option grind.warning true` to discourage its use."
  withMainContext do
    let extracted? ← grindExtract (← getMainGoal) config only params sketch
    if let some extracted := extracted? then
      logInfoAt ref extracted
    else
      replaceMainGoal []

open Parser.Tactic in
syntax (name := Parser.Tactic.grindExtract)
    "grind" optConfig (&" only")? (" [" withoutPosition(grindParam,*) "]")? " extract" term : tactic

-- Corresponds to `Lean.Elab.Tactic.evalGrind`.
@[tactic Parser.Tactic.grindExtract] def evalGrindExtract : Tactic := fun stx => do
  match stx with
  | `(tactic| grind $config:optConfig $[only%$only]? $[[$params:grindParam,*]]? extract $sketch:term) =>
    let config ← elabGrindConfig config
    let sketch ← elabSketch sketch
    discard <| evalGrindExtractCore stx config only params sketch
  | _ => throwUnsupportedSyntax
