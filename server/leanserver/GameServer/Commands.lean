import Lean

import GameServer.EnvExtensions

open Lean Meta

set_option autoImplicit false

/-! ## Easy metadata -/

section metadata

open Lean Meta Elab Command Term

/-- Create a game with the given identifier as name. -/
elab "Game" n:str : command => do
  let name := n.getString
  setCurGameId name
  if (← getGame? name).isNone then
    insertGame name {name}

/-- Create a World -/
elab "World" n:str : command => do
  let name := n.getString
  setCurWorldId name
  if ¬ (← getCurGame).worlds.nodes.contains name then
    addWorld {name}

/-- Define the current level number. -/
elab "Level" level:num : command => do
  let level := level.getNat
  setCurLevelIdx level
  addLevel {index := level}

/-- Define the title of the current game/world/level. -/
elab "Title" t:str : command => do
  match ← getCurLayer with
  | .Level => modifyCurLevel fun level => pure {level with title := t.getString}
  | .World => modifyCurWorld  fun world => pure {world with title := t.getString}
  | .Game => modifyCurGame  fun game => pure {game with title := t.getString}

/-- Define the introduction of the current game/world/level. -/
elab "Introduction" t:str : command => do
  match ← getCurLayer with
  | .Level => modifyCurLevel fun level => pure {level with introduction := t.getString}
  | .World => modifyCurWorld  fun world => pure {world with introduction := t.getString}
  | .Game => modifyCurGame  fun game => pure {game with introduction := t.getString}

-- TODO: Instead of this, it would be nice to have a proper syntax parser that enables
-- us highlighting on the client side.
partial def reprintCore : Syntax → Option Format
  | Syntax.missing => none
  | Syntax.atom _ val => val.trim
  | Syntax.ident _ rawVal _ _ => rawVal.toString
  | Syntax.node _ kind args =>
    match args.toList.filterMap reprintCore with
    | [] => none
    | [arg] => arg
    | args => Format.group <| Format.nest 2 <| Format.joinSep args " "

def reprint (stx : Syntax) : Format :=
  reprintCore stx |>.getD ""

-- macro mods:declModifiers "lemma" n:declId sig:declSig val:declVal : command => `($mods:declModifiers theorem $n $sig $val)

/-- Define the statement of the current level.

Arguments:
- ident: (Optional) The name of the statemtent.
- descr: The human-readable version of the lemma as string. Accepts Markdown and Mathjax.
-/
elab "Statement" statementName:ident ? descr:str sig:declSig val:declVal : command => do

  let lvlIdx ← getCurLevelIdx
  let defaultDeclName : Name := (← getCurGame).name ++ (← getCurWorld).name ++
    ("level" ++ toString lvlIdx : String)
  let thmStatement ← `(theorem $(mkIdent defaultDeclName) $sig $val)
  -- let thmStatement' ← match statementName with
  -- | none => `(lemma $(mkIdent "XX") $sig $val) -- TODO: Make it into an `example`
  -- | some name => `(lemma $name $sig $val)

  let scope ← getScope
  let env ← getEnv

  elabCommand thmStatement
  modifyCurLevel fun level => pure {level with
    module := env.header.mainModule
    goal := sig,
    scope := scope,
    descrText := descr.getString,
    descrFormat := match statementName with
    | none => "example " ++ (toString <| reprint sig.raw) ++ " := by"
    | some name => (Format.join ["lemma ", reprint name.raw, " ", reprint sig.raw, " := by"]).pretty 10  -- "lemma "  ++ (toString <| reprint name.raw) ++ " " ++ (Format.pretty (reprint sig.raw) 40) ++ " := by"
  } -- Format.pretty <| format thmStatement.raw }

/-- Define the conclusion of the current game or current level if some
building a level. -/
elab "Conclusion" t:str : command => do
  match ← getCurLayer with
  | .Level => modifyCurLevel fun level => pure {level with conclusion := t.getString}
  | .World => modifyCurWorld  fun world => pure {world with conclusion := t.getString}
  | .Game => modifyCurGame  fun game => pure {game with conclusion := t.getString}

-- /-- Print current game for debugging purposes. -/
-- elab "PrintCurGame" : command => do
--   logInfo (toJson (← getCurGame))

/-- Print current level for debugging purposes. -/
elab "PrintCurLevel" : command => do
  logInfo (repr (← getCurLevel))

-- /-- Print levels for debugging purposes. -/
elab "PrintLevels" : command => do
  logInfo $ repr $ (← getCurWorld).levels.toArray

def Parser.path := Parser.sepBy1Indent Parser.ident "→"

elab "Path" s:Parser.path : command => do
  let mut last : Option Name := none
  for stx in s.raw.getArgs.getEvenElems do
    let some l := last
      | do
          last := some stx.getId
          continue
    modifyCurGame fun game =>
      pure {game with worlds := {game.worlds with edges := game.worlds.edges.push (l, stx.getId)}}
    last := some stx.getId

end metadata

/-! ## Hints -/

open Lean Meta Elab Command Term

declare_syntax_cat mydecl
syntax "(" ident ":" term ")" : mydecl

def getIdent : TSyntax `mydecl → Ident
| `(mydecl| ($n:ident : $_t:term)) => n
| _ => default

def getType : TSyntax `mydecl → Term
| `(mydecl| ($_n:ident : $t:term)) => t
| _ => default

/-- From a term `s` and a list of pairs `(i, t) ; Ident × Term`, create the syntax
where `s` is preceded with universal quantifiers `∀ i : t`. -/
def mkGoalSyntax (s : Term) : List (Ident × Term) → MacroM Term
| (n, t)::tail => do return (← `(∀ $n : $t, $(← mkGoalSyntax s tail)))
| [] => return s

/-- Declare a hint. This version doesn't prevent the unused linter variable from running. -/
local elab "Hint'" decls:mydecl* ":" goal:term "=>" msg:str : command => do
  let g ← liftMacroM $ mkGoalSyntax goal (decls.map (λ decl => (getIdent decl, getType decl))).toList
  let g ← liftTermElabM do (return ← elabTermAndSynthesize g none)
  modifyCurLevel fun level => pure {level with hints := level.hints.push {
    goal := g,
    intros := decls.size,
    text := msg.getString }}

/--
Declare a hint. This version doesn't prevent the unused linter variable from running.
A hidden hint is only displayed if explicitly requested by the user.
-/
local elab "HiddenHint'" decls:mydecl* ":" goal:term "=>" msg:str : command => do
  let g ← liftMacroM $ mkGoalSyntax goal (decls.map (λ decl => (getIdent decl, getType decl))).toList
  let g ← liftTermElabM do (return ← elabTermAndSynthesize g none)
  modifyCurLevel fun level => pure {level with hints := level.hints.push {
    goal := g,
    intros := decls.size,
    hidden := true,
    text := msg.getString }}


/-- Declare a hint in reaction to a given tactic state in the current level. -/
macro "Hint" decls:mydecl* ":" goal:term "=>" msg:str : command => do
  `(set_option linter.unusedVariables false in Hint' $decls* : $goal => $msg)

/-- Declare a hidden hint in reaction to a given tactic state in the current level. -/
macro "HiddenHint" decls:mydecl* ":" goal:term "=>" msg:str : command => do
  `(set_option linter.unusedVariables false in HiddenHint' $decls* : $goal => $msg)

/-! ## Inventory -/

/-- Throw an error if inventory doc does not exist -/
def checkInventoryDoc (type : InventoryType) (name : Name) : CommandElabM Unit := do
  let some _ := (inventoryDocExt.getState (← getEnv)).find?
      (fun x => x.name == name && x.type == type)
    | throwError "Missing {type} Documentation: {name}"

/-! ### Tactics -/

/-- Declare a documentation entry for some tactic.
Expect an identifier and then a string literal. -/
elab "TacticDoc" name:ident content:str : command =>
  modifyEnv (inventoryDocExt.addEntry · {
    category := default
    type := .Tactic
    name := name.getId,
    userName := name.getId,
    content := content.getString })

/-- Declare tactics that are introduced by this level. -/
elab "NewTactics" args:ident* : command => do
  let names := args.map (·.getId)
  for name in names do checkInventoryDoc .Tactic name
  modifyCurLevel fun level => pure {level with tactics := {level.tactics with new := names}}

/-- Declare tactics that are temporarily disabled in this level -/
elab "DisabledTactics" args:ident* : command => do
  let names := args.map (·.getId)
  for name in names do checkInventoryDoc .Tactic name
  modifyCurLevel fun level => pure {level with tactics := {level.tactics with disabled := names}}

/-- Temporarily disable all tactics except the ones declared here -/
elab "OnlyTactics" args:ident* : command => do
  let names := args.map (·.getId)
  for name in names do checkInventoryDoc .Tactic name
  modifyCurLevel fun level => pure {level with tactics := {level.tactics with only := names}}

/-! ### Definitions -/

/-- Declare a documentation entry for some definition.
Expect an identifier and then a string literal. -/
elab "DefinitionDoc" name:ident content:str : command =>
  modifyEnv (inventoryDocExt.addEntry · {
    category := default
    type := .Definition
    name := name.getId,
    userName := name.getId,
    content := content.getString })

/-- Declare definitions that are introduced by this level. -/
elab "NewDefinitions" args:ident* : command => do
  let names := args.map (·.getId)
  for name in names do checkInventoryDoc .Definition name
  modifyCurLevel fun level => pure {level with definitions := {level.definitions with new := names}}

/-- Declare definitions that are temporarily disabled in this level -/
elab "DisabledDefinitions" args:ident* : command => do
  let names := args.map (·.getId)
  for name in names do checkInventoryDoc .Definition name
  modifyCurLevel fun level => pure {level with definitions := {level.definitions with disabled := names}}

/-- Temporarily disable all definitions except the ones declared here -/
elab "OnlyDefinitions" args:ident* : command => do
  let names := args.map (·.getId)
  for name in names do checkInventoryDoc .Definition name
  modifyCurLevel fun level => pure {level with definitions := {level.definitions with only := names}}


/-! ### Lemmas -/

/-- Declare a documentation entry for some lemma.
Expect two identifiers and then a string literal. The first identifier is meant
as the real name of the lemma while the second is the displayed name. Currently
the real name isn't used. -/
elab "LemmaDoc" name:ident "as" userName:ident "in" category:str content:str : command =>
  modifyEnv (inventoryDocExt.addEntry · {
    name := name.getId,
    type := .Lemma
    userName := userName.getId,
    category := category.getString,
    content := content.getString })

/-- Declare lemmas that are introduced by this level. -/
elab "NewLemmas" args:ident* : command => do
  let names := args.map (·.getId)
  for name in names do checkInventoryDoc .Lemma name
  modifyCurLevel fun level => pure {level with lemmas := {level.lemmas with new := names}}

/-- Declare lemmas that are temporarily disabled in this level -/
elab "DisabledLemmas" args:ident* : command => do
  let names := args.map (·.getId)
  for name in names do checkInventoryDoc .Lemma name
  modifyCurLevel fun level => pure {level with lemmas := {level.lemmas with disabled := names}}

/-- Temporarily disable all lemmas except the ones declared here -/
elab "OnlyLemmas" args:ident* : command => do
  let names := args.map (·.getId)
  for name in names do checkInventoryDoc .Lemma name
  modifyCurLevel fun level => pure {level with lemmas := {level.lemmas with only := names}}

/-! ## Make Game -/

def GameLevel.getInventory (level : GameLevel) : InventoryType → InventoryInfo
| .Tactic => level.tactics
| .Definition => level.definitions
| .Lemma => level.lemmas

def GameLevel.setComputedInventory (level : GameLevel) : InventoryType → Array Availability → GameLevel
| .Tactic, v =>     {level with tactics     := {level.tactics     with computed := v}}
| .Definition, v => {level with definitions := {level.definitions with computed := v}}
| .Lemma, v =>      {level with lemmas      := {level.lemmas      with computed := v}}

/-- Make the final Game. This command will precompute various things about the game, such as which
tactics are available in each level etc. -/
elab "MakeGame" : command => do
  let game ← getCurGame

  -- Check for loops in world graph
  if game.worlds.hasLoops then
    throwError "World graph has loops!"

  -- Compute which inventory items are available in which level:
  for inventoryType in open InventoryType in #[Tactic, Definition, Lemma] do
    let mut newItemsInWorld : HashMap Name (HashSet Name) := {}
    let mut allItems : HashSet Name := {}
    for (worldId, world) in game.worlds.nodes.toArray do
      let mut newItems : HashSet Name := {}
      for (_, level) in world.levels.toArray do
        newItems := newItems.insertMany (level.getInventory inventoryType).new
        allItems := allItems.insertMany (level.getInventory inventoryType).new
      newItemsInWorld := newItemsInWorld.insert worldId newItems

    -- Basic inventory item availability: all locked, none disabled.
    let Availability₀ : HashMap Name Availability :=
      HashMap.ofList $
        allItems.toList.map fun name =>
          (name, {name, locked := true, disabled := false})

    -- Availability after a given world
    let mut itemsInWorld : HashMap Name (HashMap Name Availability) := {}
    for (worldId, _) in game.worlds.nodes.toArray do
      let mut items := Availability₀
      let predecessors := game.worlds.predecessors worldId
      for predWorldId in predecessors do
        for item in newItemsInWorld.find! predWorldId do
          items := items.insert item {name := item, locked := false, disabled := false}
      itemsInWorld := itemsInWorld.insert worldId items

    for (worldId, world) in game.worlds.nodes.toArray do
      let mut items := itemsInWorld.find! worldId

      let levels := world.levels.toArray.insertionSort fun a b => a.1 < b.1

      for (levelId, level) in levels do
        for item in (level.getInventory inventoryType).new do
          items := items.insert item {name := item, locked := false, disabled := false}
        for item in (level.getInventory inventoryType).disabled do
          items := items.insert item {name := item, locked := false, disabled := true}

        let itemsArray := items.toArray
          |>.insertionSort (fun a b => a.1.toString < b.1.toString)
          |>.map (·.2)

        modifyLevel ⟨← getCurGameId, worldId, levelId⟩ fun level => do
          return level.setComputedInventory inventoryType itemsArray
