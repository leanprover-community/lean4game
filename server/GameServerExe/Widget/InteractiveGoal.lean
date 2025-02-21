import Lean.Widget.InteractiveGoal

/-!
This file is a modified copy of `Lean.Widget.InteractiveGoal`.

We add a field `isAssumption?` to `InteractiveHypothesisBundle`, and
`addInteractiveHypothesisBundle` populates this new field.

Everything else is just copy-pasted in order to use the modified structure.
-/

namespace GameServer.Widget
open Lean Widget

open Server

/-
Extend the interactive hypothesis bundle with an option to distinguish
"assumptions" from "objects". "Assumptions" are hypotheses of type `Prop`.
-/
@[inherit_doc Lean.Widget.InteractiveHypothesisBundle]
structure InteractiveHypothesisBundle extends Lean.Widget.InteractiveHypothesisBundle where
  /-- The hypothesis's type is of type `Prop` -/
  isAssumption? : Option Bool := none
deriving RpcEncodable

-- duplicated but with custom `InteractiveHypothesisBundle`
@[inherit_doc Lean.Widget.InteractiveGoalCore]
structure InteractiveGoalCore where
  /-- (GameServer) use custom `InteractiveHypothesisBundle` -/
  hyps : Array InteractiveHypothesisBundle
  /-- The target type. -/
  type : CodeWithInfos
  /-- Metavariable context that the goal is well-typed in. -/
  ctx : WithRpcRef Elab.ContextInfo

-- duplicated but with custom `InteractiveGoalCore`
@[inherit_doc Lean.Widget.InteractiveGoal]
structure InteractiveGoal extends InteractiveGoalCore where
  /-- The name `foo` in `case foo`, if any. -/
  userName? : Option String
  /-- The symbol to display before the target type. Usually `⊢ ` but `conv` goals use `∣ `
  and it could be extended. -/
  goalPrefix : String
  /-- Identifies the goal (ie with the unique name of the MVar that it is a goal for.) -/
  mvarId : MVarId
  /-- If true, the goal was not present on the previous tactic state. -/
  isInserted? : Option Bool := none
  /-- If true, the goal will be removed on the next tactic state. -/
  isRemoved? : Option Bool := none
  deriving RpcEncodable

-- duplicated with custom `InteractiveGoalCore`
@[inherit_doc Lean.Widget.InteractiveTermGoal]
structure InteractiveTermGoal extends InteractiveGoalCore where
  /-- Syntactic range of the term. -/
  range : Lsp.Range
  /-- Information about the term whose type is the term-mode goal. -/
  term : WithRpcRef Elab.TermInfo
  deriving RpcEncodable

-- duplicated with custom `InteractiveGoalCore`
-- @[inherit_doc Lean.Widget.InteractiveGoalCore.pretty]
def InteractiveGoalCore.pretty (g : InteractiveGoalCore) (userName? : Option String)
    (goalPrefix : String) : Format := Id.run do
  let indent := 2 -- Use option
  let mut ret := match userName? with
    | some userName => f!"case {userName}"
    | none          => Format.nil
  for hyp in g.hyps do
    ret := addLine ret
    let names := hyp.names
        |>.toList
        |>.filter (· != toString Name.anonymous)
        |> " ".intercalate
    match names with
    | "" =>
      ret := ret ++ Format.group f!":{Format.nest indent (Format.line ++ hyp.type.stripTags)}"
    | _ =>
      match hyp.val? with
      | some val =>
        ret := ret ++ Format.group f!"{names} : {hyp.type.stripTags} :={Format.nest indent (Format.line ++ val.stripTags)}"
      | none =>
        ret := ret ++ Format.group f!"{names} :{Format.nest indent (Format.line ++ hyp.type.stripTags)}"
  ret := addLine ret
  ret ++ f!"{goalPrefix}{Format.nest indent g.type.stripTags}"
where
  addLine (fmt : Format) : Format :=
    if fmt.isNil then fmt else fmt ++ Format.line

-- duplicated with custom `InteractiveGoal`
-- @[inherit_doc Lean.Widget.InteractiveGoal.pretty]
def InteractiveGoal.pretty (g : InteractiveGoal) : Format :=
  g.toInteractiveGoalCore.pretty g.userName? g.goalPrefix

-- duplicated with custom `InteractiveTermGoal`
-- @[inherit_doc Lean.Widget.InteractiveTermGoal.pretty]
def InteractiveTermGoal.pretty (g : InteractiveTermGoal) : Format :=
  g.toInteractiveGoalCore.pretty none "⊢ "

-- duplicated with custom `InteractiveGoal`
-- @[inherit_doc Lean.Widget.InteractiveGoals]
structure InteractiveGoals where
  goals : Array InteractiveGoal
  deriving RpcEncodable

-- duplicated with custom `InteractiveGoals`
-- @[inherit_doc Lean.Widget.InteractiveGoals.append]
def InteractiveGoals.append (l r : InteractiveGoals) : InteractiveGoals where
  goals := l.goals ++ r.goals

instance : Append InteractiveGoals := ⟨InteractiveGoals.append⟩
instance : EmptyCollection InteractiveGoals := ⟨{goals := #[]}⟩

open Meta in
-- duplicated with custom `InteractiveHypothesisBundle` and therefore added `isAssumption?`
@[inherit_doc Lean.Widget.addInteractiveHypothesisBundle]
def addInteractiveHypothesisBundle (hyps : Array InteractiveHypothesisBundle)
    (ids : Array (String × FVarId)) (type : Expr) (value? : Option Expr := none) :
    MetaM (Array InteractiveHypothesisBundle) := do
  if ids.size == 0 then
    throwError "Can only add a nonzero number of ids as an InteractiveHypothesisBundle."
  let fvarIds := ids.map Prod.snd
  let names := ids.map Prod.fst
  return hyps.push {
    names
    fvarIds
    type        := (← ppExprTagged type)
    val?        := (← value?.mapM ppExprTagged)
    isInstance? := if (← isClass? type).isSome then true else none
    isType?     := if (← instantiateMVars type).isSort then true else none
    -- (GameServer) Added:
    isAssumption? := if (← inferType type).isProp then true else none
  }

-- `withGoalCtx` seems to be unmodified

-- Duplicated from `Lean.Widget.goalToInteractive` with custom structures
open Meta in
@[inherit_doc Lean.Widget.goalToInteractive]
def goalToInteractive (mvarId : MVarId) : MetaM InteractiveGoal := do
  let ppAuxDecls := pp.auxDecls.get (← getOptions)
  let ppImplDetailHyps := pp.implementationDetailHyps.get (← getOptions)
  let showLetValues := pp.showLetValues.get (← getOptions)
  withGoalCtx mvarId fun lctx mvarDecl => do
    let pushPending (ids : Array (String × FVarId)) (type? : Option Expr) (hyps : Array InteractiveHypothesisBundle)
        : MetaM (Array InteractiveHypothesisBundle) :=
      if ids.isEmpty then
        pure hyps
      else
        match type? with
        | none      => pure hyps
        | some type => addInteractiveHypothesisBundle hyps ids type
    let mut varNames : Array (String × FVarId) := #[]
    let mut prevType? : Option Expr := none
    let mut hyps : Array InteractiveHypothesisBundle := #[]
    for localDecl in lctx do
      if !ppAuxDecls && localDecl.isAuxDecl || !ppImplDetailHyps && localDecl.isImplementationDetail then
        continue
      else
        match localDecl with
        | LocalDecl.cdecl _index fvarId varName type _ _ =>
          let varName := toString varName
          let type ← instantiateMVars type
          if prevType? == none || prevType? == some type then
            varNames := varNames.push (varName, fvarId)
          else
            hyps ← pushPending varNames prevType? hyps
            varNames := #[(varName, fvarId)]
          prevType? := some type
        | LocalDecl.ldecl _index fvarId varName type val _ _ => do
          let varName := toString varName
          hyps ← pushPending varNames prevType? hyps
          let type ← instantiateMVars type
          let val? ← if showLetValues then pure (some (← instantiateMVars val)) else pure none
          hyps ← addInteractiveHypothesisBundle hyps #[(varName, fvarId)] type val?
          varNames := #[]
          prevType? := none
    hyps ← pushPending varNames prevType? hyps
    let goalTp ← instantiateMVars mvarDecl.type
    let goalFmt ← ppExprTagged goalTp
    let userName? := match mvarDecl.userName with
      | Name.anonymous => none
      | name           => some <| toString name.eraseMacroScopes
    return {
      hyps
      type := goalFmt
      ctx := ⟨{← Elab.CommandContextInfo.save with }⟩
      userName?
      goalPrefix := getGoalPrefix mvarDecl
      mvarId
    }

end GameServer.Widget
