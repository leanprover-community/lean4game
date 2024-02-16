import GameServer.AbstractCtx

/-!
This file contains anything related to the `Hint` tactic used to add hints to a game level.
-/

open Lean Meta Elab

namespace GameServer

syntax hintArg := atomic(" (" (&"strict" <|> &"hidden") " := " withoutPosition(term) ")")

/-- A hint to help the user with a specific goal state -/
structure GoalHintEntry where
  goal : AbstractCtxResult
  /-- Text of the hint as an expression of type `Array Expr → MessageData` -/
  text : Expr
  rawText : String
  /-- If true, then hint should be hidden and only be shown on player's request -/
  hidden : Bool := false
  /-- If true, then the goal must contain only the assumptions specified in `goal` and no others -/
  strict : Bool := false

instance : Repr GoalHintEntry := {
  reprPrec := fun a n => reprPrec a.text n
}

/-- For a hint `(hint : GoalHintEntry)` one uses `(← evalHintMessage hint.text) x`
 where `(x : Array Expr)` contains the names of all the variables that should be inserted
 in the text.

 TODO: explain better. -/
unsafe def evalHintMessageUnsafe : Expr → MetaM (Array Expr → MessageData) :=
  evalExpr (Array Expr → MessageData)
    (.forallE default (mkApp (mkConst ``Array [levelZero]) (mkConst ``Expr))
      (mkConst ``MessageData) .default)

@[implemented_by evalHintMessageUnsafe]
def evalHintMessage : Expr → MetaM (Array Expr → MessageData) := fun _ => pure (fun _ => "")

/-- Remove any spaces at the beginning of a new line -/
partial def removeIndentation (s : String) : String :=
  let rec loop (i : String.Pos) (acc : String) (removeSpaces := false) : String :=
    let c := s.get i
    let i := s.next i
    if s.atEnd i then
      acc.push c
    else if removeSpaces && c == ' ' then
      loop i acc (removeSpaces := true)
    else if c == '\n' then
      loop i (acc.push c) (removeSpaces := true)
    else
      loop i (acc.push c)
  loop ⟨0⟩ ""

/-- A tactic that can be used inside `Statement`s to indicate in which proof states players should
see hints. The tactic does not affect the goal state.
-/
elab (name := GameServer.Tactic.Hint) "Hint" args:hintArg* msg:interpolatedStr(term) : tactic => do
  let mut strict := false
  let mut hidden := false

  -- remove spaces at the beginning of new lines
  let msg := TSyntax.mk $ msg.raw.setArgs $ ← msg.raw.getArgs.mapM fun m => do
    match m with
    | Syntax.node info k args =>
      if k == interpolatedStrLitKind && args.size == 1 then
        match args.get! 0 with
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
    let textmvar ← mkFreshExprMVar none
    guard $ ← isDefEq textmvar text -- Store the text in a mvar.
    -- The information about the hint is logged as a message using `logInfo` to transfer it to the
    -- `Statement` command:
    logInfo $
      .tagged `Hint $
      .nest (if strict then 1 else 0) $
      .nest (if hidden then 1 else 0) $
      .compose (.ofGoal textmvar.mvarId!) (.ofGoal goal)
