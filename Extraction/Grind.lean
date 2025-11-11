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
  let e ← mvarsToGrind e
  let e := e.replaceFVars oldFVars (newFVars.take oldFVars.size)
  let e ← Grind.unfoldReducible e
  Core.betaReduce e
where
  mvarsToGrind (e : Expr) : MetaM Expr := do
    let { expr, mvars, .. } ← Meta.abstractMVars e (levels := false)
    let mut e := expr
    for mvar in mvars do
      let type ← mvar.mvarId!.getType
      let fresh ← mkFreshExprMVar type
      e := mkApp e fresh
    return e

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

protected inductive Result.Success where
  /-- `grind` succeeded. -/
  | grind
  /-- `grind` failed and extraction succeeded. -/
  | extraction (ex : Expr)

protected inductive Result where
  /-- Neither `grind`, nor extraction succeeded. -/
  | failure (result : Grind.Result)
  /-- `grind` succeeded. -/
  | success (s : Extraction.Result.Success)

abbrev Result.grind : Extraction.Result :=
  .success .grind

abbrev Result.extraction (ex : Expr) : Extraction.Result :=
  .success (.extraction ex)

-- Corresponds to `Lean.Meta.Grind.main`.
protected def main (target : MVarId) (params : Params) (sketch : Sketch) :
    MetaM Extraction.Result := do
  profileitM Exception "grind" (← getOptions) do
    let oldFVars ← getLocalHyps
    GrindM.runAtGoal target params fun goal => do
      let failure? ← solve goal
      let some failedGoal := failure? | return .grind
      let (ex?, _) ← GoalM.run failedGoal do onFailure target sketch oldFVars
      let some ex := ex? | return .failure (← mkResult params failure?)
      return .extraction ex

end Lean.Meta.Grind.Extraction

namespace Lean.Elab.Tactic.Extraction

-- Corresponds to `Lean.Meta.Grind.withProtectedMCtx`.
def withProtectedMCtx
    (abstractProof : Bool) (mvarId : MVarId) (k : MVarId → TacticM Result.Success) :
    TacticM Unit := do
  let mvarId ← mvarId.abstractMVars
  let mvarId ← mvarId.clearImplDetails
  tryCatchRuntimeEx (main mvarId) fun ex => do
    mvarId.admit
    throw ex
where
  main (mvarId : MVarId) : TacticM Unit := mvarId.withContext do
    let type ← mvarId.getType
    let proof? : Option Expr ← withNewMCtxDepth do
      let mvar' ← mkFreshExprSyntheticOpaqueMVar type
      let success ← k mvar'.mvarId!
      match success with
      | .grind        => return ← finalize mvar'
      | .extraction _ => return none
    if let some proof := proof? then
      mvarId.assign proof
      replaceMainGoal []
    else /- if extracted -/
      -- When calling `withProtectedMCtx`, the goal `mvarId` is immediately assigned by
      -- `abstractMVars` and `clearImplDetails` and is therefore not a goal from the point of view
      -- of `TacticM` anymore (it still shows up in `getGoals`, but not in `getMainGoal`, as the
      -- latter filters out assigned mvars). We therefore need to push the (new/updated) goal mvar
      -- back onto the list of goals.
      pushGoal mvarId
  finalize (mvar' : Expr) : MetaM Expr := do
    trace[grind.debug.proof] "{← instantiateMVars mvar'}"
    let type ← inferType mvar'
    -- `grind` proofs are often big, if `abstractProof` is true, we create an auxiliary theorem.
    let val ← if !abstractProof then
      instantiateMVarsProfiling mvar'
    else if (← isProp type) then
      mkAuxTheorem type (← instantiateMVarsProfiling mvar') (zetaDelta := true)
    else
      let auxName ← mkAuxDeclName `grind
      mkAuxDefinition auxName type (← instantiateMVarsProfiling mvar') (zetaDelta := true)
    return val

declare_syntax_cat grindExtractPrefix
syntax "grind" optConfig (&" only")? (" [" withoutPosition(grindParam,*) "]")? : grindExtractPrefix

declare_syntax_cat grindExtractHead
syntax grindExtractPrefix " extract" : grindExtractHead

-- TODO: How does one properly turn `Syntax` into `MessageData` (instead of `.raw.prettyPrint`)?
def grindSufficesSuggestion (ex : Expr) (sketch : Syntax) (pre : TSyntax `grindExtractPrefix) :
    TacticM TryThis.Suggestion := do
  let msg := m!"suffices «{sketch.prettyPrint}» : {← ppExpr ex} by {pre.raw.prettyPrint}"
  msg.toString

def grindPlainSuggestion (pre : TSyntax `grindExtractPrefix) : TryThis.Suggestion where
  suggestion := .tsyntax pre

-- Corresponds to `Lean.Elab.Tactic.grind`.
protected def «grind»
    (mvarId : MVarId) (config : Grind.Config) (only : Bool) (ps : TSyntaxArray ``grindParam)
    (head : TSyntax `grindExtractHead) (sketch : Term) : TacticM Unit := do
  if debug.terminalTacticsAsSorry.get (← getOptions) then
    mvarId.admit
  mvarId.withContext do
    let params ← mkGrindParams config only ps mvarId
    withProtectedMCtx config.abstractProof mvarId fun mvarId' => do
      let s ← Sketch.elabSketch sketch
      let result ← Extraction.main mvarId' params s
      let `(grindExtractHead| $pre:grindExtractPrefix extract) := head | unreachable!
      match result with
      | .failure res =>
        throwError "`grind extract` failed\n{← res.toMessageData}"
      | .success .grind =>
        logWarningAt head "`grind` succeeded, extraction is redundant"
        let suggestion := grindPlainSuggestion pre
        TryThis.addSuggestion head suggestion (origSpan? := ← getRef)
        return .grind
      | .success (.extraction ex) =>
        let suggestion ← grindSufficesSuggestion ex sketch pre
        TryThis.addSuggestion head suggestion (origSpan? := ← getRef)
        return .extraction ex

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
    Extraction.grind (← getMainGoal) config only params head sketch

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
