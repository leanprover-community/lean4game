import GameApi.Helpers
import GameApi.Inventory
import I18n

/-!
 # Inventory

The inventory contains docs for tactics, theorems, and definitions. These are all locked
in the first level and get enabled during the game.
-/

namespace GameServer

open Lean

/-! ## Doc entries -/

/-- Documentation entry of a tactic. Example:

```
/-- `rw` stands for rewrite, etc. -/
TacticDoc rw

/-- `rw` stands for rewrite, etc. -/
TacticDoc rw in "Equalities" insert "rw [$,]"
```

* The identifier is the tactics name. Some need to be escaped like `«have»`.
* The string after `in` is the category to group tactics by (in the Inventory).
* The string after `insert` is what clicking the tactic in the inventory inserts, with
  slots where the hypotheses and theorems clicked afterwards go, from left to right:
  * `$_`: a single one, afterwards the next slot is filled
  * `$,`: a comma-separated list, like in `rw [$,]`
  * `$+`: a space-separated list, like in `exact $+`
  * `$;`: a sequence of tactics separated by `;`, like in `have $_ : $+ := by $;`
  * `$$`: a literal `$`

  For example `apply $_ at $+`, or `tauto` without any slot. The default is the tactic's
  name followed by `$+`.
* The description is a string supporting Markdown.
 -/
elab doc:docComment ? "TacticDoc" name:ident inArg?:((" in " str)?)
    insertArg?:((&" insert " str)?) content:str ? : command => do
  let doc ← parseDocCommentLegacy doc content
  let doc ← doc.translate
  let cat : String := if !inArg?.raw.isNone then (⟨inArg?.raw[1]⟩ : TSyntax `str).getString else "📖︎"
  let insert : String := if insertArg?.raw.isNone then
      s!"{name.getId.toString (escape := false)} $+"
    else
      (⟨insertArg?.raw[1]⟩ : TSyntax `str).getString
  modifyEnv (inventoryTemplateExt.addEntry · {
    type := .Tactic
    name := name.getId
    displayName := name.getId.toString
    category := cat
    content := doc
    insert := insert })

/-- Documentation entry of a theorem. Example:

```
/-- says `0 < n.succ`, etc. -/
TheoremDoc Nat.succ_pos as "succ_pos"

/-- says `0 < n.succ`, etc. -/
TheoremDoc Nat.succ_pos as "succ_pos" in "Nat" insert "Nat.succ_pos"
```

* The first identifier is used in the commands `[New/Only/Disabled]Theorem`.
  It is preferably the true name of the theorem. However, this is not required.
* The string following `as` is the displayed name (in the Inventory).
* The identifier after `in` is the category to group theorems by (in the Inventory).
* The string after `insert` is what clicking the theorem in the inventory inserts.
  The default is the first identifier.
* The description is a string supporting Markdown.

Use `[[mathlib_doc]]` in the string to insert a link to the mathlib doc page. This requires
The theorem/definition to have the same fully qualified name as in mathlib.
 -/
elab doc:docComment ? "TheoremDoc" name:ident "as" displayName:str inArg?:((" in " str)?)
    insertArg?:((&" insert " str)?) content:str ? : command => do
  let doc ← parseDocCommentLegacy doc content
  let doc ← doc.translate
  let cat : String := if !inArg?.raw.isNone then (⟨inArg?.raw[1]⟩ : TSyntax `str).getString else "📖︎"
  let insert : Option String := if insertArg?.raw.isNone then none else
    some (⟨insertArg?.raw[1]⟩ : TSyntax `str).getString
  modifyEnv (inventoryTemplateExt.addEntry · {
    type := .Theorem
    name := name.getId
    category := cat
    displayName := displayName.getString
    content := doc
    insert := insert })
-- TODO: Catch the following behaviour.
-- 1. if `TheoremDoc` appears in the same file as `Statement`, it will silently use
-- it but display the info that it wasn't found in `Statement`
-- 2. if it appears in a later file, however, it will silently not do anything and keep
-- the first one.


/-- Documentation entry of a definition. Example:

```
/-- defined as `Injective f ∧ Surjective`, etc. -/
DefinitionDoc Function.Bijective as "Bijective"

/-- defined as `Injective f ∧ Surjective`, etc. -/
DefinitionDoc Function.Bijective as "Bijective" in "Fun" insert "Function.Bijective"
```

* The first identifier is used in the commands `[New/Only/Disabled]Definition`.
  It is preferably the true name of the definition. However, this is not required.
* The string following `as` is the displayed name (in the Inventory).
* The string after `in` is the category to group definitions by (in the Inventory).
* The string after `insert` is what clicking the definition in the inventory inserts.
  The default is the first identifier.
* The description is a string supporting Markdown.

Use `[[mathlib_doc]]` in the string to insert a link to the mathlib doc page. This requires
The theorem/definition to have the same fully qualified name as in mathlib.
 -/
elab doc:docComment ? "DefinitionDoc" name:ident "as" displayName:str inArg?:((" in " str)?)
    insertArg?:((&" insert " str)?) template:str ? : command => do
  let doc ← parseDocCommentLegacy doc template
  let doc ← doc.translate
  let cat : String := if !inArg?.raw.isNone then (⟨inArg?.raw[1]⟩ : TSyntax `str).getString else "📖︎"
  let insert : Option String := if insertArg?.raw.isNone then none else
    some (⟨insertArg?.raw[1]⟩ : TSyntax `str).getString
  modifyEnv (inventoryTemplateExt.addEntry · {
    type := .Definition
    name := name.getId
    displayName := displayName.getString
    category := cat
    content := doc
    insert := insert })

/-! ## Add inventory items -/

open Elab.Command in
def checkCommandNotDuplicated (items : Array Name) (cmd := "Command") : CommandElabM Unit := do
  if ¬ items.isEmpty then
    logWarning s!"You should only use one `{cmd}` per level, but it takes multiple arguments: `{cmd} obj₁ obj₂ obj₃`!"

/-- Declare tactics that are introduced by this level. -/
elab "NewTactic" args:ident* : command => do
  checkCommandNotDuplicated ((←getCurLevel).tactics.new) "NewTactic"
  for name in args do
    checkInventoryDoc .Tactic name -- TODO: Add (template := "[docstring]")
  modifyCurLevel fun level => pure {level with
    tactics := {level.tactics with new := level.tactics.new ++ args.map (·.getId)}}

/-- Declare tactics that are introduced by this level but do not show up in inventory. -/
elab "NewHiddenTactic" args:ident* : command => do
  checkCommandNotDuplicated ((←getCurLevel).tactics.hidden) "NewHiddenTactic"
  modifyCurLevel fun level => pure {level with
    tactics := {level.tactics with new := level.tactics.new ++ args.map (·.getId),
                                   hidden := level.tactics.hidden ++ args.map (·.getId)}}

/-- Declare theorems that are introduced by this level. -/
elab "NewTheorem" args:ident* : command => do
  checkCommandNotDuplicated ((←getCurLevel).theorems.new) "NewTheorem"
  for name in args do
    try let _decl ← getConstInfo name.getId catch
      | _ => logErrorAt name m!"unknown identifier '{name}'."
    checkInventoryDoc .Theorem name -- TODO: Add (template := "[mathlib]")
  modifyCurLevel fun level => pure {level with
    theorems := {level.theorems with new := args.map (·.getId)}}

/-- Declare definitions that are introduced by this level. -/
elab "NewDefinition" args:ident* : command => do
  checkCommandNotDuplicated ((←getCurLevel).definitions.new) "NewDefinition"
  for name in args do checkInventoryDoc .Definition name -- TODO: Add (template := "[mathlib]")
  modifyCurLevel fun level => pure {level with
    definitions := {level.definitions with new := args.map (·.getId)}}

/-- Declare tactics that are temporarily disabled in this level.
This is ignored if `OnlyTactic` is set. -/
elab "DisabledTactic" args:ident* : command => do
  checkCommandNotDuplicated ((←getCurLevel).tactics.disabled) "DisabledTactic"
  for name in args do checkInventoryDoc .Tactic name
  modifyCurLevel fun level => pure {level with
    tactics := {level.tactics with disabled := args.map (·.getId)}}

/-- Declare theorems that are temporarily disabled in this level.
This is ignored if `OnlyTheorem` is set. -/
elab "DisabledTheorem" args:ident* : command => do
  checkCommandNotDuplicated ((←getCurLevel).theorems.disabled) "DisabledTheorem"
  for name in args do checkInventoryDoc .Theorem name
  modifyCurLevel fun level => pure {level with
    theorems := {level.theorems with disabled := args.map (·.getId)}}

/-- Declare definitions that are temporarily disabled in this level -/
elab "DisabledDefinition" args:ident* : command => do
  checkCommandNotDuplicated ((←getCurLevel).definitions.disabled) "DisabledDefinition"
  for name in args do checkInventoryDoc .Definition name
  modifyCurLevel fun level => pure {level with
    definitions := {level.definitions with disabled := args.map (·.getId)}}

/-- Temporarily disable all tactics except the ones declared here -/
elab "OnlyTactic" args:ident* : command => do
  checkCommandNotDuplicated ((←getCurLevel).tactics.only) "OnlyTactic"
  for name in args do checkInventoryDoc .Tactic name
  modifyCurLevel fun level => pure {level with
    tactics := {level.tactics with only := args.map (·.getId)}}

/-- Temporarily disable all theorems except the ones declared here -/
elab "OnlyTheorem" args:ident* : command => do
  checkCommandNotDuplicated ((←getCurLevel).theorems.only) "OnlyTheorem"
  for name in args do checkInventoryDoc .Theorem name
  modifyCurLevel fun level => pure {level with
    theorems := {level.theorems with only := args.map (·.getId)}}

/-- Temporarily disable all definitions except the ones declared here.
This is ignored if `OnlyDefinition` is set. -/
elab "OnlyDefinition" args:ident* : command => do
  checkCommandNotDuplicated ((←getCurLevel).definitions.only) "OnlyDefinition"
  for name in args do checkInventoryDoc .Definition name
  modifyCurLevel fun level => pure {level with
    definitions := {level.definitions with only := args.map (·.getId)}}

/-- Define which tab of Theorems is opened by default. Usage: `TheoremTab "Nat"`.
If omitted, the current tab will remain open. -/
elab "TheoremTab"  category:str : command =>
  modifyCurLevel fun level => pure {level with theoremTab := category.getString}
