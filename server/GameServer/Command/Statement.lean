import Lean
import GameServer.Tactic.LetIntros
import GameServer.Layer.Extension
import GameServer.Lean.DocComment
import GameServer.Inventory
import I18n

open Lean Meta Elab Command

namespace GameServer

set_option autoImplicit false


/-! # Exercise Statement -/

/-- You can write `Statement add_comm (preamble := simp) .... := by` which
will automatically execute the given tactic sequence before the exercise
is handed to the player.

A common example is to use

```
refine { carrier := M, ?.. }
```

in exercises, where the statement is a structure, to fill in all the data fields.

For example in "Show that all matrices with first column zero form a submodule",
you could provide the set of all these matrices as `carrier` and the player will receive
all the `Prop`-valued fields as goals.
-/
syntax preambleArg := atomic("(" "preamble" " := " withoutPosition(tacticSeq) ")")
-- TODO: is this fix correct?

/-- Define the statement of the current level. -/
elab doc:docComment ? attrs:Parser.Term.attributes ?
    "Statement" statementName:ident ? preamble:preambleArg ? sig:declSig val:declVal : command => do
  let lvlIdx ← getCurLevelIdx

  -- Add an optional tactic sequence that the engine executes before the game starts
  let preambleSeq : TSyntax `Lean.Parser.Tactic.tacticSeq ← match preamble with
  | some arg => match arg with
    | `(preambleArg| (preamble := $tac)) => pure tac
    | _ => `(Parser.Tactic.tacticSeq| skip)
  | none => `(Parser.Tactic.tacticSeq| skip)

  -- Translate the docstring of the `Statement`
  let docComment : Option String ← match (← parseDocComment doc) with
  | none => pure none
  | some d => d.translate

  -- Save the messages before evaluation of the proof.
  let initMsgs ← modifyGet fun st => (st.messages, { st with messages := {} })

  -- The default name of the statement is `[Game].[World].level[no.]`, e.g. `NNG.Addition.level1`
  -- However, this should not be used when designing the game.
  let defaultDeclName : Ident := mkIdent <| (← getCurGame).name ++ (← getCurWorld).name ++
    (.mkSimple <| "level" ++ toString lvlIdx)

  -- Collect all used tactics/theorems in the sample proof:
  let usedInventory : UsedInventory ← match val with
  | `(Parser.Command.declVal| := $proof:term) => do
    collectUsedInventory proof
  | _ => throwError "expected `:=`"

  -- modify the proof to start with `let_intros` and any specified preamble sequence.
  let modifiedVal ← match val with
  | `(Parser.Command.declVal| := by $proof) =>
    `(Parser.Command.declVal| := by {let_intros; $(⟨preambleSeq⟩); $(⟨proof⟩)})
  | _ => panic "Expected `:= by`!"

  -- Add theorem to context.
  match statementName with
  | some name =>
    let env ← getEnv
    let fullName := (← getCurrNamespace) ++ name.getId
    if env.contains fullName then
      let some orig := env.constants.map₁.get? fullName
        | throwError s!"error in \"Statement\": `{fullName}` not found."
      let origType := orig.type
      -- TODO: Check if `origType` agrees with `sig` and output `logInfo` instead of `logWarning`
      -- in that case.
      logWarningAt name (m!"Environment already contains {fullName}! Only the existing " ++
      m!"statement will be available in later levels:\n\n{origType}")
      let thmStatement ← `(command| $[$doc]? $[$attrs:attributes]? theorem $defaultDeclName $sig $modifiedVal)
      elabCommand thmStatement
      -- Check that statement has a docs entry.
      checkInventoryDoc .Theorem name (name := fullName) (template := docComment)
    else
      let thmStatement ← `(command| $[$doc]? $[$attrs:attributes]? theorem $name $sig $modifiedVal)
      elabCommand thmStatement
      -- Check that statement has a docs entry.
      checkInventoryDoc .Theorem name (name := fullName) (template := docComment)
  | none =>
    let thmStatement ← `(command| $[$doc]? $[$attrs:attributes]? theorem $defaultDeclName $sig $modifiedVal)
    elabCommand thmStatement

  let msgs := (← get).messages
  let mut hints := #[]
  let mut nonHintMsgs := #[]
  for msg in msgs.toArray do
    -- Look for messages produced by the `Hint` tactic. They are used to pass information about the
    -- intermediate goal state
    if let MessageData.withNamingContext _ $ MessageData.withContext ctx $
        .tagged `Hint $
        .nest strict $
        .nest hidden $
        .nest defeq $
        .compose (.ofGoal text) (.ofGoal goal) := msg.data then
      let hint ← liftTermElabM $ withMCtx ctx.mctx $ withLCtx ctx.lctx #[] $ withEnv ctx.env do

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
          hintFVarsNames := hintFVarsNames.push <| Expr.fvar ⟨.mkSimple s!"«\{{name₁}}»"⟩

        let text ← instantiateMVars (mkMVar text)

        -- Evaluate the text in the `Hint`'s context to get the old variable names.
        let rawText := (← GameServer.evalHintMessage text) hintFVarsNames
        let ctx₂ := {env := ← getEnv, mctx := ← getMCtx, lctx := ← getLCtx, opts := {}}
        let rawText : String ← (MessageData.withContext ctx₂ rawText).toString

        return {
          goal := ← abstractCtx goal
          text := text
          rawText := rawText
          strict := strict == 1
          hidden := hidden == 1
          defeq := defeq == 1
        }

      -- Note: The current setup for hints is a bit convoluted, but for now we need to
      -- send the text once through i18n to register it in the env extension.
      -- This could probably be rewritten once i18n works fully.
      let _ ← hint.rawText.translate

      hints := hints.push hint
    else
      nonHintMsgs := nonHintMsgs.push msg

  -- restore saved messages and non-hint messages
  modify fun st => { st with
    messages := initMsgs ++ {unreported := nonHintMsgs.toPArray'}
  }

  let scope ← getScope
  let env ← getEnv

  -- TODO: Is this desired or would it be better to get `elabCommand` above to ignore
  -- the namespace?
  let currNamespace ← getCurrNamespace

  -- Format theorem statement for displaying
  let sigString := sig.raw.reprint.getD ""
  let descrFormat : String := match statementName with
  | some name =>  s!"theorem {name.getId} {sigString} := by"
  | none => s!"example {sigString} := by"

  modifyCurLevel fun level => pure { level with
    module := env.header.mainModule
    goal := sig,
    preamble := preambleSeq
    scope := scope,
    descrText := docComment
    statementName := match statementName with
    | none => default
    | some name => currNamespace ++ name.getId
    descrFormat := descrFormat
    hints := hints
    tactics := {level.tactics with used := usedInventory.tactics.toArray}
    definitions := {level.definitions with used := usedInventory.definitions.toArray}
    theorems := {level.theorems with used := usedInventory.theorems.toArray}
    }



-- TODO: Notes for testing if a declaration has the simp attribute

-- -- Test: From zulip
-- section test

-- open Lean Meta Elab Command Tactic Simp

-- def Lean.Meta.SimpTheorems.hasAttribute (d : SimpTheorems) (decl : Name) :=
--   d.isTheorem (.decl decl) || d.isDeclToUnfold decl

-- def isInSimpset (simpAttr decl: Name) : CoreM Bool := do
--   let .some simpDecl ←getSimpExtension? simpAttr | return false
--   return (← simpDecl.getTheorems).hasAttribute decl

-- end test
