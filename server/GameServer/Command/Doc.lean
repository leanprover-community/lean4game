import GameServer.Layer.Extension
import I18n
import GameServer.Helpers
import GameServer.Util.CommandNotDuplicated
import GameServer.Inventory

/-! ## Doc entries -/

namespace GameServer

open Lean

/-- Documentation entry of a tactic. Example:

```
TacticDoc rw "`rw` stands for rewrite, etc. "
```

* The identifier is the tactics name. Some need to be escaped like `«have»`.
* The description is a string supporting Markdown.
 -/
elab doc:docComment ? "TacticDoc" name:ident content:str ? : command => do
  let doc ← parseDocCommentLegacy doc content
  let doc ← doc.translate
  modifyEnv (inventoryTemplateExt.addEntry · {
    type := .Tactic
    name := name.getId
    displayName := name.getId.toString
    content := doc })

/-- Documentation entry of a theorem. Example:

```
TheoremDoc Nat.succ_pos as "succ_pos" in "Nat" "says `0 < n.succ`, etc."
```

* The first identifier is used in the commands `[New/Only/Disabled]Theorem`.
  It is preferably the true name of the theorem. However, this is not required.
* The string following `as` is the displayed name (in the Inventory).
* The identifier after `in` is the category to group theorems by (in the Inventory).
* The description is a string supporting Markdown.

Use `[[mathlib_doc]]` in the string to insert a link to the mathlib doc page. This requires
The theorem/definition to have the same fully qualified name as in mathlib.
 -/
elab doc:docComment ? "TheoremDoc" name:ident "as" displayName:str "in" category:str content:str ? :
    command => do
  let doc ← parseDocCommentLegacy doc content
  let doc ← doc.translate
  modifyEnv (inventoryTemplateExt.addEntry · {
    type := .Theorem
    name := name.getId
    category := category.getString
    displayName := displayName.getString
    content := doc })
-- TODO: Catch the following behaviour.
-- 1. if `TheoremDoc` appears in the same file as `Statement`, it will silently use
-- it but display the info that it wasn't found in `Statement`
-- 2. if it appears in a later file, however, it will silently not do anything and keep
-- the first one.


/-- Documentation entry of a definition. Example:

```
DefinitionDoc Function.Bijective as "Bijective" "defined as `Injective f ∧ Surjective`, etc."
```

* The first identifier is used in the commands `[New/Only/Disabled]Definition`.
  It is preferably the true name of the definition. However, this is not required.
* The string following `as` is the displayed name (in the Inventory).
* The description is a string supporting Markdown.

Use `[[mathlib_doc]]` in the string to insert a link to the mathlib doc page. This requires
The theorem/definition to have the same fully qualified name as in mathlib.
 -/
elab doc:docComment ? "DefinitionDoc" name:ident "as" displayName:str template:str ? : command => do
  let doc ← parseDocCommentLegacy doc template
  let doc ← doc.translate
  modifyEnv (inventoryTemplateExt.addEntry · {
    type := .Definition
    name := name.getId,
    displayName := displayName.getString,
    content := doc })

/-- Declare tactics that are introduced by this level. -/
elab "NewTactic" args:ident* : command => do
  checkCommandNotDuplicated ((←getCurLevel).tactics.new) "NewTactic"
  for name in ↑args do
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
  for name in ↑args do
    try let _decl ← getConstInfo name.getId catch
      | _ => logErrorAt name m!"unknown identifier '{name}'."
    checkInventoryDoc .Theorem name -- TODO: Add (template := "[mathlib]")
  modifyCurLevel fun level => pure {level with
    theorems := {level.theorems with new := args.map (·.getId)}}

/-- Declare definitions that are introduced by this level. -/
elab "NewDefinition" args:ident* : command => do
  checkCommandNotDuplicated ((←getCurLevel).definitions.new) "NewDefinition"
  for name in ↑args do checkInventoryDoc .Definition name -- TODO: Add (template := "[mathlib]")
  modifyCurLevel fun level => pure {level with
    definitions := {level.definitions with new := args.map (·.getId)}}

/-- Declare tactics that are temporarily disabled in this level.
This is ignored if `OnlyTactic` is set. -/
elab "DisabledTactic" args:ident* : command => do
  checkCommandNotDuplicated ((←getCurLevel).tactics.disabled) "DisabledTactic"
  for name in ↑args do checkInventoryDoc .Tactic name
  modifyCurLevel fun level => pure {level with
    tactics := {level.tactics with disabled := args.map (·.getId)}}

/-- Declare theorems that are temporarily disabled in this level.
This is ignored if `OnlyTheorem` is set. -/
elab "DisabledTheorem" args:ident* : command => do
  checkCommandNotDuplicated ((←getCurLevel).theorems.disabled) "DisabledTheorem"
  for name in ↑args  do checkInventoryDoc .Theorem name
  modifyCurLevel fun level => pure {level with
    theorems := {level.theorems with disabled := args.map (·.getId)}}

/-- Declare definitions that are temporarily disabled in this level -/
elab "DisabledDefinition" args:ident* : command => do
  checkCommandNotDuplicated ((←getCurLevel).definitions.disabled) "DisabledDefinition"
  for name in ↑args do checkInventoryDoc .Definition name
  modifyCurLevel fun level => pure {level with
    definitions := {level.definitions with disabled := args.map (·.getId)}}

/-- Temporarily disable all tactics except the ones declared here -/
elab "OnlyTactic" args:ident* : command => do
  checkCommandNotDuplicated ((←getCurLevel).tactics.only) "OnlyTactic"
  for name in ↑args do checkInventoryDoc .Tactic name
  modifyCurLevel fun level => pure {level with
    tactics := {level.tactics with only := args.map (·.getId)}}

/-- Temporarily disable all theorems except the ones declared here -/
elab "OnlyTheorem" args:ident* : command => do
  checkCommandNotDuplicated ((←getCurLevel).theorems.only) "OnlyTheorem"
  for name in ↑args do checkInventoryDoc .Theorem name
  modifyCurLevel fun level => pure {level with
    theorems := {level.theorems with only := args.map (·.getId)}}

/-- Temporarily disable all definitions except the ones declared here.
This is ignored if `OnlyDefinition` is set. -/
elab "OnlyDefinition" args:ident* : command => do
  checkCommandNotDuplicated ((←getCurLevel).definitions.only) "OnlyDefinition"
  for name in ↑args do checkInventoryDoc .Definition name
  modifyCurLevel fun level => pure {level with
    definitions := {level.definitions with only := args.map (·.getId)}}

/-- Define which tab of Theorems is opened by default. Usage: `TheoremTab "Nat"`.
If omitted, the current tab will remain open. -/
elab "TheoremTab"  category:str : command =>
  modifyCurLevel fun level => pure {level with theoremTab := category.getString}
