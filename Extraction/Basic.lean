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
  /-- The result of extraction: the extracted term, equivalent to the proof goal. -/
  result     : Expr
  /-- Proves `result = target`/`result ≍ target`. -/
  eqHEqProof : Expr

def extract (target : Expr) (sketch : Sketch) : GoalM (Option Extracted) := do
  let .minAST := sketch | throwError "`grind extract` currently only supports the `min_ast` sketch"
  let (internalizedTarget, result) ← extractMinAST target
  let eqHEqProof ← mkEqHEqProof result internalizedTarget
  return some { result, eqHEqProof }

inductive ExtractResult where
  | extracted (ex : Extracted)
  | grind (result : Grind.Result)

-- Note: The replacement of fvars may be sketchy, as while `grind` sets `preserveOrder := true` when
--       calling `revertAll`, I'm not sure if there are other aspects which may affect the order of
--       fvars in `grind`'s local context. For example, does `intros` preserve the order?
def Lean.Expr.toGrind (oldFVars newFVars : Array Expr) (e : Expr) : MetaM Expr := do
  let e := e.replaceFVars oldFVars (newFVars.take oldFVars.size)
  let e ← Grind.unfoldReducible e
  Core.betaReduce e

-- NOTE: We just translate the fvars back naively for now, as our goal is first to test different
--       kinds of extraction, so it's ok if this fails sometimes.
def Lean.Expr.fromGrind (oldFVars newFVars : Array Expr) (e : Expr) : Expr :=
  e.replaceFVars (newFVars.take oldFVars.size) oldFVars

def Extracted.fromGrind (oldFVars newFVars : Array Expr) (ex : Extracted) : Extracted where
  result     := ex.result.fromGrind oldFVars newFVars
  eqHEqProof := ex.eqHEqProof.fromGrind oldFVars newFVars

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
          let target ← target.toGrind oldFVars newFVars
          let some ex ← extract target sketch | return none
          return some <| ex.fromGrind oldFVars newFVars
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
