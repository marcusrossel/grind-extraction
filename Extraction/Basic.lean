import Extraction.Sketch
import Extraction.Lean
open Lean Meta Elab Term Tactic Grind

def extractMinAST (target : Expr) : GoalM (Expr × Expr) := do
  let target ← shareCommon target
  let min ← foldEqc target target fun node min => do
    let expr := node.self
    if expr.isFalse then return min
    if expr.sizeWithoutSharing < min.sizeWithoutSharing then return expr else return min
  return (target, min)

structure Extracted where
  /-- The goal in whose context the following expressions are defined.
      This is relevant for validity of fvars and mvars. -/
  goal       : MVarId
  /-- The result of extraction: the extracted term, equivalent to the proof goal. -/
  result     : Expr
  /-- The internalized type of the proof goal. -/
  target     : Expr
  /-- Proves `result = target`/`result ≍ target`. -/
  eqHEqProof : Expr

def extract (target : Expr) (sketch : Sketch) : GoalM (Option Extracted) := do
  let .minAST := sketch | throwError "`grind extract` currently only supports the `min_ast` sketch"
  let (internalizedTarget, result) ← extractMinAST target
  let eqHEqProof ← mkEqHEqProof result internalizedTarget
  let grindGoal := (← get).mvarId
  return some { result, target := internalizedTarget, goal := grindGoal, eqHEqProof }

inductive ExtractResult where
  | extracted (ex : Extracted)
  | grind (result : Grind.Result)

private inductive GrindSolveState where
  | solved (result : Grind.Result)
  | failed (originalGoal failedGoal : Goal) (methods : MethodsRef) (context : Meta.Grind.Context) (state : Meta.Grind.State)

-- Corresponds to `Lean.Meta.Grind.main`.
def grindExtractMain (target : MVarId) (params : Params) (sketch : Sketch) : MetaM ExtractResult := do
  profileitM Exception "grind" (← getOptions) do
    let oldFVars ← getLocalHyps
    GrindM.runAtGoal target params fun goal => do
      let failure? ← solve goal
      if let some failedGoal := failure? then
        let (extracted?, _) ← GoalM.run failedGoal do
          let newFVars ← getLocalHyps
          let target ← target.getType
          let target := target.replaceFVars oldFVars (newFVars.take oldFVars.size)
          extract target sketch
        if let some extracted := extracted? then
          return .extracted extracted
      return .grind (← mkResult params failure?)

-- Corresponds to `Lean.Elab.Tactic.grind`.
def grindExtract
    (mvarId : MVarId) (config : Grind.Config)
    (only : Bool) (ps : TSyntaxArray ``Parser.Tactic.grindParam) (sketch : Sketch)
    : TacticM (Option Extracted) := do
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
    | .extracted extracted =>
      return extracted
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
      replaceGoal extracted
    else
      replaceMainGoal []
where
  replaceGoal (extracted : Extracted) : TacticM Unit := do
    -- TODO: Is there an order in which we can assign the mvars, so that fvars remain in the correct
    --       contexts? I think we can't avoid moving `extracted.result` back to the outer context.
    --       This is problematic as there may be some variables in grind's context which were still
    --       in the goal in the outer context.
    let goal ← getMainGoal
    let tag ← goal.getTag
    let newGoal ← mkFreshExprSyntheticOpaqueMVar extracted.result tag
    let proof ← mkEqHEqMP extracted.eqHEqProof newGoal
    goal.assign proof
    replaceMainGoal [newGoal.mvarId!]

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
