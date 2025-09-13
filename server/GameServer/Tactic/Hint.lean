import GameServer.EnvExtensions
import GameServer.Hints
import I18n

namespace GameServer.Tactic

open Lean Meta Elab

/-- A tactic that can be used inside `Statement`s to indicate in which proof states players should
see hints. The tactic does not affect the goal state.
-/
elab (name := Hint) "Hint" args:hintArg* msg:interpolatedStr(term) : tactic => do
  let mut strict := false
  let mut hidden := false

  -- remove spaces at the beginning of new lines
  let msg := TSyntax.mk $ msg.raw.setArgs $ ← msg.raw.getArgs.mapM fun m => do
    match m with
    | Syntax.node info k args =>
      if k == interpolatedStrLitKind && args.size == 1 then
        match args[0]! with
        | (Syntax.atom info' val) =>
          let val := removeIndentation val
          return Syntax.node info k #[Syntax.atom info' val]
        | _ => return m
      else
        return m
    | _ => return m

  for arg in args do
    match arg with
    | `(hintArg| (strict := true)) => strict := true
    | `(hintArg| (strict := false)) => strict := false
    | `(hintArg| (hidden := true)) => hidden := true
    | `(hintArg| (hidden := false)) => hidden := false
    | _ => throwUnsupportedSyntax

  let goal ← Tactic.getMainGoal
  goal.withContext do
    let abstractedGoal ← abstractCtx goal
    -- We construct an expression that can produce the hint text. The difficulty is that we
    -- want the text to possibly contain quotation of the local variables which might have been
    -- named differently by the player.
    let varsName := `vars
    let text ← withLocalDeclD varsName (mkApp (mkConst ``Array [levelZero]) (mkConst ``Expr)) fun vars => do
      let mut text ← `(m! $msg)
      let goalDecl ← goal.getDecl
      let decls := goalDecl.lctx.decls.toArray.filterMap id
      for i in [:decls.size] do
        text ← `(let $(mkIdent decls[i]!.userName) := $(mkIdent varsName)[$(quote i)]!; $text)
      return ← mkLambdaFVars #[vars] $ ← Term.elabTermAndSynthesize text none


    let goalDecl ← goal.getDecl
    let fvars := goalDecl.lctx.decls.toArray.filterMap id |> Array.map (·.fvarId)

    -- NOTE: This code about `hintFVarsNames` is duplicated from `RpcHandlers`
    -- where the variable bijection is constructed, and they
    -- need to be matching.
    -- NOTE: This is a bit a hack of somebody who does not know how meta-programming works.
    -- All we want here is a list of `userNames` for the `FVarId`s in `hintFVars`...
    -- and we wrap them in `«{}»` here since I don't know how to do it later.
    let mut hintFVarsNames : Array Expr := #[]
    for fvar in fvars do
      let name₁ ← fvar.getUserName
      hintFVarsNames := hintFVarsNames.push <| Expr.fvar ⟨s!"«\{{name₁}}»"⟩

    -- Evaluate the text in the `Hint`'s context to get the old variable names.
    let rawText := (← GameServer.evalHintMessage text) hintFVarsNames
    let ctx₂ := {env := ← getEnv, mctx := ← getMCtx, lctx := ← getLCtx, opts := {}}
    let rawText : String := (← (MessageData.withContext ctx₂ rawText).toString).dropSingleNewlines

    -- i18n
    rawText.markForTranslation

    modifyCurLevel fun level => pure {level with hints := level.hints.push {
      text := text,
      hidden := hidden,
      strict := strict,
      goal := abstractedGoal,
      rawText := rawText
    }}
