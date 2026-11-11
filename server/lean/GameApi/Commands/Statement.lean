import GameApi.Helpers
import GameApi.Inventory
import GameApi.Tactic.LetIntros
import I18n

/-! # Exercise Statement -/

namespace GameServer

open Lean Elab.Command


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
syntax preambleArg := atomic("(" &"preamble" ":=" withoutPosition(tacticSeq) ")")

/-- Define the statement of the current level. -/
elab doc:docComment ? attrs:Parser.Term.attributes ?
    "Statement" statementName:ident ? preamble:preambleArg ? sig:declSig val:declVal : command => do
  let lvlIdx ← getCurLevelIdx

  let optSig := declSig.toOptDeclSig sig
  let isProp ← declSig.isProp sig

  -- add an optional tactic sequence that the engine executes before the game starts
  let preambleSeq : TSyntax ``Lean.Parser.Tactic.tacticSeq ← match preamble with
  | none => `(Parser.Tactic.tacticSeq|skip)
  | some x => match x with
    | `(preambleArg| (preamble := $tac)) => pure tac
    | _ => `(Parser.Tactic.tacticSeq|skip)

  let docContent ← parseDocComment doc
  let docContent ← match docContent with
  | none => pure none
  | some d => d.translate

  -- The default name of the statement is `[Game].[World].level[no.]`, e.g. `NNG.Addition.level1`
  -- However, this should not be used when designing the game.
  let defaultDeclName : Ident := mkIdent <| (← getCurGame).name ++ (← getCurWorld).name ++
    ("level" ++ toString lvlIdx : String)

  -- Collect all used tactics/theorems in the sample proof:
  let usedInventory ← match val with
  | `(Parser.Command.declVal| := $proof:term) => do
    collectUsedInventory proof
  | _ => throwError "expected `:=`"

  -- extract the `tacticSeq` from `val` in order to add `let_intros` in front.
  -- TODO: don't understand meta-programming enough to avoid having `let_intros`
  -- duplicated three times below…
  let tacticStx : TSyntax `Lean.Parser.Tactic.tacticSeq := match val with
  | `(Parser.Command.declVal| := by $proof) => proof
  | _ => panic "expected `:= by`"

  -- Add theorem to context.
  match statementName with
  | some name =>
    let env ← getEnv
    let fullName := (← getCurrNamespace) ++ name.getId
    let inventoryType : InventoryType := if isProp then .Theorem else .Definition
    if env.contains fullName then
      let some orig := env.constants.map₁.get? fullName
        | throwError s!"error in \"Statement\": `{fullName}` not found."
      let origType := orig.type
      -- TODO: Check if `origType` agrees with `sig` and output `logInfo` instead of `logWarning`
      -- in that case.
      logWarningAt name (m!"Environment already contains {fullName}! Only the existing " ++
      m!"statement will be available in later levels:\n\n{origType}")
      let thmStatement ← match isProp with
        | true => `(command| $[$doc]? $[$attrs:attributes]? theorem $defaultDeclName $sig := by {let_intros; $(⟨preambleSeq⟩); $(⟨tacticStx⟩)})
        | false => `(command| $[$doc]? $[$attrs:attributes]? def $defaultDeclName $optSig := by {let_intros; $(⟨preambleSeq⟩); $(⟨tacticStx⟩)})
      elabCommand thmStatement
      -- Check that statement has a docs entry.
      checkInventoryDoc inventoryType name (name := fullName) (template := docContent)
    else
      let thmStatement ← match isProp with
        | true => `(command| $[$doc]? $[$attrs:attributes]? theorem $name $sig := by {let_intros; $(⟨preambleSeq⟩); $(⟨tacticStx⟩)})
        | false => `(command| $[$doc]? $[$attrs:attributes]? def $name $optSig := by {let_intros; $(⟨preambleSeq⟩); $(⟨tacticStx⟩)})
      elabCommand thmStatement
      -- Check that statement has a docs entry.
      checkInventoryDoc inventoryType name (name := fullName) (template := docContent)
  | none =>
    let thmStatement ← match isProp with
      | true => `(command| $[$doc]? $[$attrs:attributes]? theorem $defaultDeclName $sig := by {let_intros; $(⟨preambleSeq⟩); $(⟨tacticStx⟩)})
      | false => `(command| $[$doc]? $[$attrs:attributes]? def $defaultDeclName $optSig := by {let_intros; $(⟨preambleSeq⟩); $(⟨tacticStx⟩)})
    elabCommand thmStatement

  let scope ← getScope
  let env ← getEnv

  -- TODO: Is this desired or would it be better to get `elabCommand` above to ignore
  -- the namespace?
  let currNamespace ← getCurrNamespace

  -- Format theorem statement for displaying
  let sigString := sig.raw.reprint.getD ""
  let descrFormat : String := match statementName, isProp with
  | some name, true =>  s!"theorem {name.getId} {sigString} := by"
  | some name, false =>  s!"def {name.getId} {sigString} := by"
  | none, _ => s!"example {sigString} := by" -- TODO: is this correct?

  modifyCurLevel fun level => pure { level with
    module := env.header.mainModule
    goal := sig
    preamble := preambleSeq
    scope := scope
    descrText := docContent
    isProp := isProp
    statementName := match statementName with
    | none => default
    | some name => currNamespace ++ name.getId
    descrFormat := descrFormat
    tactics := {level.tactics with used := usedInventory.tactics.toArray}
    definitions := {level.definitions with used := usedInventory.definitions.toArray}
    theorems := {level.theorems with used := usedInventory.theorems.toArray}
    }
