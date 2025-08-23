import GameServer.Helpers
import GameServer.Inventory
import GameServer.Options
import GameServer.SaveData
import GameServer.Hints
import GameServer.Tactic.LetIntros
import GameServer.RpcHandlers -- only needed to collect the translations of "level completed" msgs
import I18n

open Lean Meta Elab Command Std

namespace GameServer

set_option autoImplicit false

/-! # Game metadata -/

/-- Switch to the specified `Game` (and create it if non-existent). Example: `Game "NNG"` -/
elab "Game" n:str : command => do
  let name := n.getString
  setCurGameId name
  if (← getGame? name).isNone then
    insertGame name {name}

/-- Create a new world in the active game. Example: `World "Addition"` -/
elab "World" n:str : command => do
  let name := n.getString
  setCurWorldId name
  if ¬ (← getCurGame).worlds.nodes.contains name then
    addWorld {name}

/-- Define the current level number. Levels inside a world must be
numbered consecutive starting with `1`. Example: `Level 1` -/
elab "Level" level:num : command => do
  let level := level.getNat
  setCurLevelIdx level
  addLevel {index := level}

/-- Define the title of the current game/world/level. -/
elab "Title" t:str : command => do
  let title ← t.getString.translate
  match ← getCurLayer with
  | .Level => modifyCurLevel fun level => pure {level with title := title}
  | .World => modifyCurWorld  fun world => pure {world with title := title}
  | .Game => modifyCurGame  fun game => pure {game with
      title := title
      tile := {game.tile with title := title}}

/-- Define the introduction of the current game/world/level. -/
elab "Introduction" t:str : command => do
  let intro ← t.getString.translate
  match ← getCurLayer with
  | .Level => modifyCurLevel fun level => pure {level with introduction := intro}
  | .World => modifyCurWorld  fun world => pure {world with introduction := intro}
  | .Game => modifyCurGame  fun game => pure {game with introduction := intro}

/-- Define the info of the current game. Used for e.g. credits -/
elab "Info" t:str : command => do
  let info ← t.getString.translate
  match ← getCurLayer with
  | .Level =>
    logError "Can't use `Info` in a level!"
    pure ()
  | .World =>
    logError "Can't use `Info` in a world"
    pure ()
  | .Game => modifyCurGame  fun game => pure {game with info := info}

/-- Provide the location of the image for the current game/world/level.
Paths are relative to the lean project's root. -/
elab "Image" t:str : command => do
  let file := t.getString
  if not <| ← System.FilePath.pathExists file then
    logWarningAt t s!"Make sure the cover image '{file}' exists."
  if not <| file.startsWith "images/" then
    logWarningAt t s!"The file name should start with `images/`. Make sure all images are in that folder."

  match ← getCurLayer with
  | .Level =>
    logWarning "Level-images not implemented yet" -- TODO
    modifyCurLevel fun level => pure {level with image := file}
  | .World =>
    modifyCurWorld  fun world => pure {world with image := file}
  | .Game =>
    logWarning "Main image of the game not implemented yet" -- TODO
    modifyCurGame  fun game => pure {game with image := file}

/-- Define the conclusion of the current game or current level if some
building a level. -/
elab "Conclusion" t:str : command => do
  let conclusion ← t.getString.translate
  match ← getCurLayer with
  | .Level => modifyCurLevel fun level => pure {level with conclusion := conclusion}
  | .World => modifyCurWorld  fun world => pure {world with conclusion := conclusion}
  | .Game => modifyCurGame  fun game => pure {game with conclusion := conclusion}

/-- A list of games that should be played before this one. Example `Prerequisites "NNG" "STG"`. -/
elab "Prerequisites" t:str* : command => do
  modifyCurGame fun game => pure {game with
    tile := {game.tile with prerequisites := t.map (·.getString) |>.toList}}

/-- Short caption for the game (1 sentence) -/
elab "CaptionShort" t:str : command => do
  let caption ← t.getString.translate
  modifyCurGame fun game => pure {game with
    tile := {game.tile with short := caption}}

/-- More detailed description what the game is about (2-4 sentences). -/
elab "CaptionLong" t:str : command => do
  let caption ← t.getString.translate
  modifyCurGame fun game => pure {game with
    tile := {game.tile with long := caption}}

/-- A list of Languages the game is translated to. For example `Languages "de" "en"`.

The keys are ISO language codes.
 -/
elab "Languages" t:str* : command => do
  modifyCurGame fun game => pure {game with
    tile := {game.tile with languages := t.map (·.getString) |>.toList}}

/-- The Image of the game (optional). TODO: Not implemented -/
elab "CoverImage" t:str : command => do
  let file := t.getString
  if not <| ← System.FilePath.pathExists file then
    logWarningAt t s!"Make sure the cover image '{file}' exists."
  if not <| file.startsWith "images/" then
    logWarningAt t s!"The file name should start with `images/`. Make sure all images are in that folder."

  modifyCurGame fun game => pure {game with
    tile := {game.tile with image := file}}

/-! # Inventory

The inventory contains docs for tactics, theorems, and definitions. These are all locked
in the first level and get enabled during the game.
-/

/-! ## Doc entries -/

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
    type := .Lemma
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

/-! ## Add inventory items -/

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
  for name in args do
    checkInventoryDoc .Tactic name (template := "")
  modifyCurLevel fun level => pure {level with
    tactics := {level.tactics with new := level.tactics.new ++ args.map (·.getId),
                                   hidden := level.tactics.hidden ++ args.map (·.getId)}}

/-- Declare theorems that are introduced by this level. -/
elab "NewTheorem" args:ident* : command => do
  checkCommandNotDuplicated ((←getCurLevel).lemmas.new) "NewTheorem"
  for name in args do
    try let _decl ← getConstInfo name.getId catch
      | _ => logErrorAt name m!"unknown identifier '{name}'."
    checkInventoryDoc .Lemma name -- TODO: Add (template := "[mathlib]")
  modifyCurLevel fun level => pure {level with
    lemmas := {level.lemmas with new := args.map (·.getId)}}

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
  checkCommandNotDuplicated ((←getCurLevel).lemmas.disabled) "DisabledTheorem"
  for name in args do checkInventoryDoc .Lemma name
  modifyCurLevel fun level => pure {level with
    lemmas := {level.lemmas with disabled := args.map (·.getId)}}

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
  checkCommandNotDuplicated ((←getCurLevel).lemmas.only) "OnlyTheorem"
  for name in args do checkInventoryDoc .Lemma name
  modifyCurLevel fun level => pure {level with
    lemmas := {level.lemmas with only := args.map (·.getId)}}

/-- Temporarily disable all definitions except the ones declared here.
This is ignored if `OnlyDefinition` is set. -/
elab "OnlyDefinition" args:ident* : command => do
  checkCommandNotDuplicated ((←getCurLevel).definitions.only) "OnlyDefinition"
  for name in args do checkInventoryDoc .Definition name
  modifyCurLevel fun level => pure {level with
    definitions := {level.definitions with only := args.map (·.getId)}}

/-- Define which tab of Lemmas is opened by default. Usage: `TheoremTab "Nat"`.
If omitted, the current tab will remain open. -/
elab "TheoremTab"  category:str : command =>
  modifyCurLevel fun level => pure {level with lemmaTab := category.getString}


/-! DEPRECATED -/

elab doc:docComment ? "LemmaDoc" name:ident "as" displayName:str "in" category:str content:str ? :
    command => do
  logWarning "Deprecated. Has been renamed to `TheoremDoc`"
  let doc ← parseDocCommentLegacy doc content
  modifyEnv (inventoryTemplateExt.addEntry · {
    type := .Lemma
    name := name.getId
    category := category.getString
    displayName := displayName.getString
    content := doc })

elab "NewLemma" args:ident* : command => do
  logWarning "Deprecated. Has been renamed to `NewTheorem`"
  checkCommandNotDuplicated ((←getCurLevel).lemmas.new) "NewLemma"
  for name in args do
    try let _decl ← getConstInfo name.getId catch
      | _ => logErrorAt name m!"unknown identifier '{name}'."
    checkInventoryDoc .Lemma name -- TODO: Add (template := "[mathlib]")
  modifyCurLevel fun level => pure {level with
    lemmas := {level.lemmas with new := args.map (·.getId)}}

elab "DisabledLemma" args:ident* : command => do
  logWarning "Deprecated. Has been renamed to `DisabledTheorem`"
  checkCommandNotDuplicated ((←getCurLevel).lemmas.disabled) "DisabledLemma"
  for name in args  do checkInventoryDoc .Lemma name
  modifyCurLevel fun level => pure {level with
    lemmas := {level.lemmas with disabled := args.map (·.getId)}}

elab "OnlyLemma" args:ident* : command => do
  logWarning "Deprecated. Has been renamed to `OnlyTheorem`"
  checkCommandNotDuplicated ((←getCurLevel).lemmas.only) "OnlyLemma"
  for name in args do checkInventoryDoc .Lemma name
  modifyCurLevel fun level => pure {level with
    lemmas := {level.lemmas with only := args.map (·.getId)}}

elab "LemmaTab"  category:str : command => do
  logWarning "Deprecated. Has been renamed to `TheoremTab`"
  modifyCurLevel fun level => pure {level with lemmaTab := category.getString}

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
syntax preambleArg := atomic("(" &"preamble" ":=" withoutPosition(tacticSeq) ")")

/-- Define the statement of the current level. -/
elab doc:docComment ? attrs:Parser.Term.attributes ?
    "Statement" statementName:ident ? preamble:preambleArg ? sig:declSig val:declVal : command => do
  let lvlIdx ← getCurLevelIdx

  -- add an optional tactic sequence that the engine executes before the game starts
  let preambleSeq : TSyntax `Lean.Parser.Tactic.tacticSeq ← match preamble with
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

  -- Collect all used tactics/lemmas in the sample proof:
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
    if env.contains fullName then
      let some orig := env.constants.map₁.get? fullName
        | throwError s!"error in \"Statement\": `{fullName}` not found."
      let origType := orig.type
      -- TODO: Check if `origType` agrees with `sig` and output `logInfo` instead of `logWarning`
      -- in that case.
      logWarningAt name (m!"Environment already contains {fullName}! Only the existing " ++
      m!"statement will be available in later levels:\n\n{origType}")
      let thmStatement ← `(command| $[$doc]? $[$attrs:attributes]? theorem $defaultDeclName $sig := by {let_intros; $(⟨preambleSeq⟩); $(⟨tacticStx⟩)})
      elabCommand thmStatement
      -- Check that statement has a docs entry.
      checkInventoryDoc .Lemma name (name := fullName) (template := docContent)
    else
      let thmStatement ← `(command| $[$doc]? $[$attrs:attributes]? theorem $name $sig := by {let_intros; $(⟨preambleSeq⟩); $(⟨tacticStx⟩)})
      elabCommand thmStatement
      -- Check that statement has a docs entry.
      checkInventoryDoc .Lemma name (name := fullName) (template := docContent)
  | none =>
    let thmStatement ← `(command| $[$doc]? $[$attrs:attributes]? theorem $defaultDeclName $sig := by {let_intros; $(⟨preambleSeq⟩); $(⟨tacticStx⟩)})
    elabCommand thmStatement

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
    descrText := docContent
    statementName := match statementName with
    | none => default
    | some name => currNamespace ++ name.getId
    descrFormat := descrFormat
    tactics := {level.tactics with used := usedInventory.tactics.toArray}
    definitions := {level.definitions with used := usedInventory.definitions.toArray}
    lemmas := {level.lemmas with used := usedInventory.lemmas.toArray}
    }

/-! # Hints -/

open GameServer in

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
    let rawText : String ← (MessageData.withContext ctx₂ rawText).toString

    -- i18n
    rawText.markForTranslation

    modifyCurLevel fun level => pure {level with hints := level.hints.push {
      text := text,
      hidden := hidden,
      strict := strict,
      goal := abstractedGoal,
      rawText := rawText
    }}


/-- This tactic allows us to execute an alternative sequence of tactics, but without affecting the
proof state. We use it to define Hints for alternative proof methods or dead ends. -/
elab (name := GameServer.Tactic.Branch) "Branch" t:tacticSeq : tactic => do
  let b ← saveState
  Tactic.evalTactic t

  -- Show an info whether the branch proofs all remaining goals.
  let gs ← Tactic.getUnsolvedGoals
  if gs.isEmpty then
    -- trace[debug] "This branch finishes the proof."
    pure ()
  else
    trace[debug] "This branch leaves open goals."

  let msgs ← Core.getMessageLog
  let gameExtState := gameExt.getState (← getEnv)

  b.restore

  Core.setMessageLog msgs
  modifyEnv (fun env => gameExt.setState env gameExtState)


/-- A hole inside a template proof that will be replaced by `sorry`. -/
elab (name := GameServer.Tactic.Hole) "Hole" t:tacticSeq : tactic => do
  Tactic.evalTactic t

/--
Iterate recursively through the Syntax, replace `Hole` with `sorry` and remove all
`Hint`/`Branch` occurrences.
-/
def replaceHoles (tacs : Syntax) : Syntax :=
  match tacs with
  | Syntax.node info kind ⟨args⟩ =>
    let newArgs := filterArgs args
    Syntax.node info kind ⟨newArgs⟩
  | other => other
where filterArgs (args : List Syntax) : List Syntax :=
  match args with
    | [] => []
    -- replace `Hole` with `sorry`.
    | Syntax.node info `GameServer.Tactic.Hole _ :: r =>
      Syntax.node info `Lean.Parser.Tactic.tacticSorry #[Syntax.atom info "sorry"] :: filterArgs r
    -- delete all `Hint` and `Branch` occurrences in the middle.
    | Syntax.node _ `GameServer.Tactic.Hint _ :: _ :: r
    | Syntax.node _ `GameServer.Tactic.Branch _ :: _ :: r =>
      filterArgs r
    -- delete `Hint` and `Branch` occurrence at the end of the tactic sequence.
    | Syntax.node _ `GameServer.Tactic.Hint _ :: []
    | Syntax.node _ `GameServer.Tactic.Branch _ :: [] =>
        []
    -- Recurse on all other Syntax.
    | a :: rest =>
      replaceHoles a :: filterArgs rest

/-- The tactic block inside `Template` will be copied into the users editor.
Use `Hole` inside the template for a part of the proof that should be replaced
with `sorry`. -/
elab "Template" tacs:tacticSeq : tactic => do
  Tactic.evalTactic tacs
  let newTacs : TSyntax `Lean.Parser.Tactic.tacticSeq := ⟨replaceHoles tacs.raw⟩
  let template ← PrettyPrinter.ppCategory `Lean.Parser.Tactic.tacticSeq newTacs
  trace[debug] s!"Template:\n{template}"
  modifyLevel (←getCurLevelId) fun level => do
    return {level with template := s!"{template}"}


-- TODO: Notes for testing if a declaration has the simp attribute

-- -- Test: From zulip
-- section test

-- open Lean Meta Elab Command Tactic Simp

-- def Lean.Meta.SimpTheorems.hasAttribute (d : SimpTheorems) (decl : Name) :=
--   d.isLemma (.decl decl) || d.isDeclToUnfold decl

-- def isInSimpset (simpAttr decl: Name) : CoreM Bool := do
--   let .some simpDecl ←getSimpExtension? simpAttr | return false
--   return (← simpDecl.getTheorems).hasAttribute decl

-- end test

/-! # Make Game -/

/-- The worlds of a game are joint by dependencies. These are
automatically computed but can also be defined with the syntax
`Dependency World₁ → World₂ → World₃`. -/
def Parser.dependency := Parser.sepBy1Indent Parser.ident "→"

/-- Manually add a dependency between two worlds.

Normally, the dependencies are computed automatically by the
tactics & lemmas used in the example
proof and the ones introduced by `NewLemma`/`NewTactic`.
Use the command `Dependency World₁ → World₂` to add a manual edge to the graph,
for example if the only dependency between the worlds is given by
the narrative. -/
elab "Dependency" s:Parser.dependency : command => do
  let mut source? : Option Name := none
  for stx in s.raw.getArgs.getEvenElems do
    let some source := source?
      | do
          source? := some stx.getId
          continue
    let target := stx.getId
    match (← getCurGame).worlds.nodes.get? target with
    | some _ => pure ()
    | none => logErrorAt stx m!"World `{target}` seems not to exist"

    modifyCurGame fun game =>
      pure {game with worlds := {game.worlds with edges := game.worlds.edges.push (source, target)}}
    source? := some target

/-- Build the game. This command will precompute various things about the game, such as which
tactics are available in each level etc. -/
elab "MakeGame" : command => do
  let game ← getCurGame

  let env ← getEnv

  -- Now create The doc entries from the templates
  for item in inventoryTemplateExt.getState env do
    let name := item.name

    let content : String ← match item.content with
    | "" =>
      -- If documentation is missing, try using the docstring instead.
      let docstring ← getDocstring env name item.type
      match docstring with
      | some ds => pure s!"*(lean docstring)*\\\n{ds}"
      | none => pure "(missing)"
    | template =>
      -- TODO: Process content template.
      -- TODO: Add information about inventory items
      pure $ template.replace "[[mathlib_doc]]"
        s!"[mathlib doc](https://leanprover-community.github.io/mathlib4_docs/find/?pattern={name}#doc)"

    match item.type with
    | .Lemma =>
      modifyEnv (inventoryExt.addEntry · { item with
        content := content
        -- Add the lemma statement to the doc
        statement := (← getStatementString name)
      })
    | _ =>
      modifyEnv (inventoryExt.addEntry · { item with
        content := content
      })

  -- For each `worldId` this contains a set of items used in this world
  let mut usedItemsInWorld : HashMap Name (HashSet Name) := {}

  -- For each `worldId` this contains a set of items newly defined in this world
  let mut newItemsInWorld : HashMap Name (HashSet Name) := {}

  -- Items that should not be displayed in inventory
  let mut hiddenItems : HashSet Name := {}

  let allWorlds := game.worlds.nodes.toArray
  let nrWorlds := allWorlds.size
  let mut nrLevels := 0

  -- Calculate which "items" are used/new in which world
  for (worldId, world) in allWorlds do
    let mut usedItems : HashSet Name := {}
    let mut newItems : HashSet Name := {}
    for inventoryType in #[.Tactic, .Definition, .Lemma] do
      for (levelId, level) in world.levels.toArray do
        usedItems := usedItems.insertMany (level.getInventory inventoryType).used
        newItems := newItems.insertMany (level.getInventory inventoryType).new
        hiddenItems := hiddenItems.insertMany (level.getInventory inventoryType).hidden

        -- if the previous level was named, we need to add it as a new lemma
        if inventoryType == .Lemma then
          match levelId with
          | 0 => pure ()
          | 1 => pure () -- level ids start with 1, so we need to skip 1, too
          | i₀ + 1 =>
            let some idx := world.levels.get? (i₀) | throwError s!"Level {i₀ + 1} not found for world {worldId}!"
            match (idx).statementName with
            | .anonymous => pure ()
            | .num _ _ => panic "Did not expect to get a numerical statement name!"
            | .str pre s =>
              let name := Name.str pre s
              newItems := newItems.insert name

          if inventoryType == .Lemma then

      -- if the last level was named, we need to add it as a new lemma
      let i₀ := world.levels.size

        let some idx := world.levels.get? (i₀) | throwError s!"Level {i₀} not found for world {worldId}!"
        match (idx).statementName with
        | .anonymous => pure ()
        | .num _ _ => panic "Did not expect to get a numerical statement name!"
        | .str pre s =>
          let name := Name.str pre s
          newItems := newItems.insert name

    usedItemsInWorld := usedItemsInWorld.insert worldId usedItems
    newItemsInWorld := newItemsInWorld.insert worldId newItems
    -- DEBUG: print new/used items
    -- logInfo m!"{worldId} uses: {usedItems.toList}"
    -- logInfo m!"{worldId} introduces: {newItems.toList}"

    -- Moreover, count the number of levels in the game
    nrLevels := nrLevels + world.levels.toArray.size

  /- for each "item" this is a HashSet of `worldId`s that introduce this item -/
  let mut worldsWithNewItem : HashMap Name (HashSet Name) := {}
  for (worldId, _world) in allWorlds do
    for newItem in newItemsInWorld.getD worldId {} do
      worldsWithNewItem := worldsWithNewItem.insert newItem $
        (worldsWithNewItem.getD newItem {}).insert worldId

  -- For each `worldId` this is a HashSet of `worldId`s that this world depends on.
  let mut worldDependsOnWorlds : HashMap Name (HashSet Name) := {}

  -- For a pair of `worldId`s `(id₁, id₂)` this is a HasSet of "items" why `id₁` depends on `id₂`.
  let mut dependencyReasons : HashMap (Name × Name) (HashSet Name) := {}

  -- Calculate world dependency graph `game.worlds`
  for (dependentWorldId, _dependentWorld) in allWorlds do
    let mut dependsOnWorlds : HashSet Name := {}
    -- Adding manual dependencies that were specified via the `Dependency` command.
    for (sourceId, targetId) in game.worlds.edges do
      if targetId = dependentWorldId then
        dependsOnWorlds := dependsOnWorlds.insert sourceId

    for usedItem in usedItemsInWorld.getD dependentWorldId {} do
      match worldsWithNewItem.get? usedItem with
      | none => logWarning m!"No world introducing {usedItem}, but required by {dependentWorldId}"
      | some worldIds =>
        -- Only need a new dependency if the world does not introduce an item itself
        if !worldIds.contains dependentWorldId then
          -- Add all worlds as dependencies which introduce this item
          -- TODO: Could do something more clever here.
          dependsOnWorlds := dependsOnWorlds.insertMany worldIds
          -- Store the dependency reasons for debugging
          for worldId in worldIds do
            let tmp := (dependencyReasons.getD (dependentWorldId, worldId) {}).insert usedItem
            dependencyReasons := dependencyReasons.insert (dependentWorldId, worldId) tmp
    worldDependsOnWorlds := worldDependsOnWorlds.insert dependentWorldId dependsOnWorlds

  -- Debugging: show all dependency reasons if the option `lean4game.showDependencyReasons` is set
  if lean4game.showDependencyReasons.get (← getOptions) then
    for (world, dependencies) in worldDependsOnWorlds.toArray do
      if dependencies.isEmpty then
        logInfo m!"Dependencies of '{world}': none"
      else
        let mut msg := m!"Dependencies of '{world}':"
        for dep in dependencies do
          match dependencyReasons.get? (world, dep) with
          | none =>
            msg := msg ++ m!"\n· '{dep}': no reason found (manually added?)"
          | some items =>
            msg := msg ++ m!"\n· '{dep}' because of:\n  {items.toList}"
        logInfo msg

  -- Check graph for loops and remove transitive edges
  let loop := findLoops worldDependsOnWorlds
  if loop != [] then
    logError m!"Loop: Dependency graph has a loop: {loop}"
    for i in [:loop.length] do
      let w1 := loop[i]!
      let w2 := loop[if i == loop.length - 1 then 0 else i + 1]!
      match dependencyReasons.get? (w1, w2) with
      -- This should not happen. Could use `find!` again...
      | none => logError m!"Did not find a reason why {w1} depends on {w2}."
      | some items =>
        logError m!"{w1} depends on {w2} because of {items.toList}."
  else
    worldDependsOnWorlds ← removeTransitive worldDependsOnWorlds

    -- need to delete all existing edges as they are already present in `worldDependsOnWorlds`.
    modifyCurGame fun game =>
      pure {game with worlds := {game.worlds with edges := Array.empty}}

    for (dependentWorldId, worldIds) in worldDependsOnWorlds.toArray do
      modifyCurGame fun game =>
        pure {game with worlds := {game.worlds with
          edges := game.worlds.edges.append (worldIds.toArray.map fun wid => (wid, dependentWorldId))}}

  -- Add the number of levels and worlds to the tile for the landing page
  modifyCurGame fun game => pure {game with tile := {game.tile with
    levels := nrLevels
    worlds := nrWorlds }}

  -- Apparently we need to reload `game` to get the changes to `game.worlds` we just made
  let game ← getCurGame

  let mut allItemsByType : HashMap InventoryType (HashSet Name) := {}
  -- Compute which inventory items are available in which level:
  for inventoryType in #[.Tactic, .Definition, .Lemma] do

    -- Which items are introduced in which world?
    let mut lemmaStatements : HashMap (Name × Nat) Name := {}
    -- TODO: I believe `newItemsInWorld` has way to many elements in it which we iterate over
    -- e.g. we iterate over `ring` for `Lemma`s as well, but so far that seems to cause no problems
    let mut allItems : HashSet Name := {}
    for (worldId, world) in game.worlds.nodes.toArray do
      let mut newItems : HashSet Name := {}
      for (levelId, level) in world.levels.toArray do
        let newLemmas := (level.getInventory inventoryType).new
        newItems := newItems.insertMany newLemmas
        allItems := allItems.insertMany newLemmas
        if inventoryType == .Lemma then
          -- For levels `2, 3, …` we check if the previous level was named
          -- in which case we add it as available lemma.
          match levelId with
          | 0 => pure ()
          | 1 => pure () -- level ids start with 1, so we need to skip 1, too.
          | i₀ + 1 =>
            -- add named statement from previous level to the available lemmas.
            let some idx := world.levels.get? (i₀) | throwError s!"Level {i₀ + 1} not found for world {worldId}!"
            match (idx).statementName with
            | .anonymous => pure ()
            | .num _ _ => panic "Did not expect to get a numerical statement name!"
            | .str pre s =>
              let name := Name.str pre s
              newItems := newItems.insert name
              allItems := allItems.insert name
              lemmaStatements := lemmaStatements.insert (worldId, levelId) name
      if inventoryType == .Lemma then
        -- if named, add the lemma from the last level of the world to the inventory
        let i₀ := world.levels.size
        match i₀ with
        | 0 => logWarning m!"World `{worldId}` contains no levels."
        | i₀ =>
          let some idx := world.levels.get? (i₀) | throwError s!"Level {i₀} not found for world {worldId}!"
          match (idx).statementName with
          | .anonymous => pure ()
          | .num _ _ => panic "Did not expect to get a numerical statement name!"
          | .str pre s =>
            let name := Name.str pre s
            newItems := newItems.insert name
            allItems := allItems.insert name
      newItemsInWorld := newItemsInWorld.insert worldId newItems

    -- Basic inventory item availability: all locked.
    let Availability₀ : HashMap Name InventoryTile :=
      HashMap.ofList $
        ← allItems.toList.mapM fun item => do
          -- Using a match statement because the error message of `Option.get!` is not helpful.
          match (← getInventoryItem? item inventoryType) with
          | none =>
            -- Note: we did have a panic here before because lemma statement and doc entry
            -- had mismatching namespaces
            logError m!"There is no inventory item ({inventoryType}) for: {item}."
            panic s!"Inventory item {item} not found!"
          | some data =>
            return (item, {
              name := item
              displayName := data.displayName
              category := data.category
              altTitle := data.statement
              hidden := hiddenItems.contains item })



    -- Availability after a given world
    let mut itemsInWorld : HashMap Name (HashMap Name InventoryTile) := {}
    for (worldId, _) in game.worlds.nodes.toArray do
      -- Unlock all items from previous worlds
      let mut items := Availability₀
      let predecessors := game.worlds.predecessors worldId
      -- logInfo m!"Predecessors: {predecessors.toArray.map fun (a) => (a)}"
      for predWorldId in predecessors do
        for item in newItemsInWorld.getD predWorldId {} do
          let data := (← getInventoryItem? item inventoryType).get!
          items := items.insert item {
            name := item
            displayName := data.displayName
            category := data.category
            locked := false
            altTitle := data.statement
            hidden := hiddenItems.contains item }
      itemsInWorld := itemsInWorld.insert worldId items

    for (worldId, world) in game.worlds.nodes.toArray do
      let mut items := itemsInWorld.getD worldId {}

      let levels := world.levels.toArray.insertionSort fun a b => a.1 < b.1

      for (levelId, level) in levels do
        let levelInfo := level.getInventory inventoryType

        -- unlock items that are unlocked in this level
        for item in levelInfo.new do
          let data := (← getInventoryItem? item inventoryType).get!
          items := items.insert item {
            name := item
            displayName := data.displayName
            category := data.category
            locked := false
            altTitle := data.statement
            hidden := hiddenItems.contains item }

        -- add the exercise statement from the previous level
        -- if it was named
        if inventoryType == .Lemma then
          match lemmaStatements.get? (worldId, levelId) with
          | none => pure ()
          | some name =>
            let data := (← getInventoryItem? name inventoryType).get!
            items := items.insert name {
              name := name
              displayName := data.displayName
              category := data.category
              altTitle := data.statement
              locked := false }

        -- add marks for `disabled` and `new` lemmas here, so that they only apply to
        -- the current level.
        let itemsArray := items.toArray
          |>.insertionSort (fun a b => a.1.toString < b.1.toString)
          |>.map (·.2)
          |>.map (fun item => { item with
            disabled := if levelInfo.only.size == 0 then
                levelInfo.disabled.contains item.name
              else
                not (levelInfo.only.contains item.name)
            new := levelInfo.new.contains item.name
            })

        modifyLevel ⟨← getCurGameId, worldId, levelId⟩ fun level => do
          return level.setComputedInventory inventoryType itemsArray
    allItemsByType := allItemsByType.insert inventoryType allItems

  let getTiles (type : InventoryType) : CommandElabM (Array InventoryTile) := do
    (allItemsByType.getD type {}).toArray.mapM (fun name => do
      let some item ← getInventoryItem? name type
        | throwError "Expected item to exist: {name}"
      return item.toTile)
  let inventory : InventoryOverview := {
    lemmas := (← getTiles .Lemma).map (fun tile => {tile with hidden := hiddenItems.contains tile.name})
    tactics := (← getTiles .Tactic).map (fun tile => {tile with hidden := hiddenItems.contains tile.name})
    definitions := (← getTiles .Definition).map (fun tile => {tile with hidden := hiddenItems.contains tile.name})
    lemmaTab := none
  }

  saveGameData allItemsByType inventory
