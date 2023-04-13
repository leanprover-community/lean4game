import GameServer.EnvExtensions

open Lean Meta Elab Command

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

/-- Define the conclusion of the current game or current level if some
building a level. -/
elab "Conclusion" t:str : command => do
  match ← getCurLayer with
  | .Level => modifyCurLevel fun level => pure {level with conclusion := t.getString}
  | .World => modifyCurWorld  fun world => pure {world with conclusion := t.getString}
  | .Game => modifyCurGame  fun game => pure {game with conclusion := t.getString}

/-! ## World Paths -/

/-- The worlds of a game are joint by paths. These are defined with the syntax
`Path World₁ → World₂ → World₃`. -/
def Parser.path := Parser.sepBy1Indent Parser.ident "→"

/-- The worlds of a game are joint by paths. These are defined with the syntax
`Path World₁ → World₂ → World₃`. -/
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



/-! # Inventory

The inventory contains docs for tactics, lemmas, and definitions. These are all disabled
in the first level and get enabled during the game.
-/

/-! ## Doc entries -/

/-- Throw an error if inventory doc does not exist -/
def checkInventoryDoc (type : InventoryType) (name : Name) : CommandElabM Unit := do
  let some _ := (inventoryDocExt.getState (← getEnv)).find?
      (fun x => x.name == name && x.type == type)
    | throwError "Missing {type} Documentation: {name} (add `{type}Doc {name}` in your game's docs section)"

/-- Documentation entry of a tactic. Example:

```
TacticDoc rw "`rw` stands for rewrite, etc. "
```

* The identifier is the tactics name. Some need to be escaped like `«have»`.
* The description is a string supporting Markdown.
 -/
elab "TacticDoc" name:ident content:str : command =>
  modifyEnv (inventoryDocExt.addEntry · {
    category := default
    type := .Tactic
    name := name.getId,
    displayName := name.getId.toString,
    content := content.getString })

/-- Documentation entry of a lemma. Example:

```
LemmaDoc Nat.succ_pos as "succ_pos" in "Nat" "says `0 < n.succ`, etc."
```

* The first identifier is used in the commands `[New/Only/Disabled]Lemma`.
  It is preferably the true name of the lemma. However, this is not required.
* The string following `as` is the displayed name (in the Inventory).
* The identifier after `in` is the category to group lemmas by (in the Inventory).
* The description is a string supporting Markdown.
 -/
elab "LemmaDoc" name:ident "as" displayName:str "in" category:str content:str : command =>
  modifyEnv (inventoryDocExt.addEntry · {
    name := name.getId,
    type := .Lemma
    displayName := displayName.getString,
    category := category.getString,
    content := content.getString })

/-- Documentation entry of a definition. Example:

```
DefinitionDoc Function.Bijective as "Bijective" "defined as `Injective f ∧ Surjective`, etc."
```

* The first identifier is used in the commands `[New/Only/Disabled]Definition`.
  It is preferably the true name of the definition. However, this is not required.
* The string following `as` is the displayed name (in the Inventory).
* The description is a string supporting Markdown.
 -/
elab "DefinitionDoc" name:ident "as" displayName:str content:str : command =>
  modifyEnv (inventoryDocExt.addEntry · {
    category := default
    type := .Definition
    name := name.getId,
    displayName := displayName.getString,
    content := content.getString })

/-! ## Add inventory items -/

/-- Declare tactics that are introduced by this level. -/
elab "NewTactic" args:ident* : command => do
  let names := args.map (·.getId)
  for name in names do checkInventoryDoc .Tactic name
  modifyCurLevel fun level => pure {level with tactics := {level.tactics with new := names}}

/-- Declare lemmas that are introduced by this level. -/
elab "NewLemma" args:ident* : command => do
  let names := args.map (·.getId)
  for name in names do checkInventoryDoc .Lemma name
  modifyCurLevel fun level => pure {level with lemmas := {level.lemmas with new := names}}

/-- Declare definitions that are introduced by this level. -/
elab "NewDefinition" args:ident* : command => do
  let names := args.map (·.getId)
  for name in names do checkInventoryDoc .Definition name
  modifyCurLevel fun level => pure {level with definitions := {level.definitions with new := names}}

/-- Declare tactics that are temporarily disabled in this level.
This is ignored if `OnlyTactic` is set. -/
elab "DisabledTactic" args:ident* : command => do
  let names := args.map (·.getId)
  -- for name in names do checkInventoryDoc .Tactic name
  modifyCurLevel fun level => pure {level with tactics := {level.tactics with disabled := names}}

/-- Declare lemmas that are temporarily disabled in this level.
This is ignored if `OnlyLemma` is set. -/
elab "DisabledLemma" args:ident* : command => do
  let names := args.map (·.getId)
  -- for name in names do checkInventoryDoc .Lemma name
  modifyCurLevel fun level => pure {level with lemmas := {level.lemmas with disabled := names}}

/-- Declare definitions that are temporarily disabled in this level -/
elab "DisabledDefinition" args:ident* : command => do
  let names := args.map (·.getId)
  -- for name in names do checkInventoryDoc .Definition name
  modifyCurLevel fun level => pure {level with definitions := {level.definitions with disabled := names}}

/-- Temporarily disable all tactics except the ones declared here -/
elab "OnlyTactic" args:ident* : command => do
  let names := args.map (·.getId)
  for name in names do checkInventoryDoc .Tactic name
  modifyCurLevel fun level => pure {level with tactics := {level.tactics with only := names}}

/-- Temporarily disable all lemmas except the ones declared here -/
elab "OnlyLemma" args:ident* : command => do
  let names := args.map (·.getId)
  for name in names do checkInventoryDoc .Lemma name
  modifyCurLevel fun level => pure {level with lemmas := {level.lemmas with only := names}}

/-- Temporarily disable all definitions except the ones declared here.
This is ignored if `OnlyDefinition` is set. -/
elab "OnlyDefinition" args:ident* : command => do
  let names := args.map (·.getId)
  for name in names do checkInventoryDoc .Definition name
  modifyCurLevel fun level => pure {level with definitions := {level.definitions with only := names}}

/-- Define which tab of Lemmas is opened by default. Usage: `LemmaTab "Nat"`.
If omitted, the current tab will remain open. -/
elab "LemmaTab"  category:str : command =>
  modifyCurLevel fun level => pure {level with lemmaTab := category.getString}



/-! # Exercise Statement -/

-- TODO: Instead of this, it would be nice to have a proper syntax parser that enables
-- us highlighting on the client side.
partial def reprintCore : Syntax → Option Format
  | Syntax.missing => none
  | Syntax.atom _ val => val.trim
  | Syntax.ident _ rawVal _ _ => rawVal.toString
  | Syntax.node _ _ args =>
    match args.toList.filterMap reprintCore with
    | [] => none
    | [arg] => arg
    | args => Format.group <| Format.nest 2 <| Format.joinSep args " "

/-- `reprint` is used to display the Lean-statement to the user-/
def reprint (stx : Syntax) : Format :=
  reprintCore stx |>.getD ""

/-- Define the statement of the current level. -/
elab "Statement" statementName:ident ? descr:str ? sig:declSig val:declVal : command => do

  -- Check that the statement name is a lemma in the doc
  match statementName with
  | some name => checkInventoryDoc .Lemma name.getId
  | none => pure Unit.unit

  let lvlIdx ← getCurLevelIdx
  let defaultDeclName : Name := (← getCurGame).name ++ (← getCurWorld).name ++
    ("level" ++ toString lvlIdx : String)

  -- save the messages before evaluation of the proof
  let initMsgs ← modifyGet fun st => (st.messages, { st with messages := {} })

  let thmStatement ← `(theorem $(mkIdent defaultDeclName) $sig $val)
  -- let thmStatement' ← match statementName with
  -- | none => `(lemma $(mkIdent "XX") $sig $val) -- TODO: Make it into an `example`
  -- | some name => `(lemma $name $sig $val)
  elabCommand thmStatement

  let msgs := (← get).messages

  let mut hints := #[]
  let mut nonHintMsgs := #[]
  for msg in msgs.msgs do
    -- Look for messages produced by the `Hint` tactic. They are used to pass information about the
    -- intermediate goal state
    if let MessageData.withNamingContext _ $ MessageData.withContext ctx $
        .tagged `Hint $
        .nest strict $
        .nest hidden $
        .compose (.ofGoal text) (.ofGoal goal) := msg.data then
      let hint ← liftTermElabM $ withMCtx ctx.mctx $ withLCtx ctx.lctx #[] $ withEnv ctx.env do
        return {
          goal := ← abstractCtx goal
          text := ← instantiateMVars (mkMVar text)
          strict := strict == 1
          hidden := hidden == 1
        }
      hints := hints.push hint
    else
      nonHintMsgs := nonHintMsgs.push msg

  -- restore saved messages and non-hint messages
  modify fun st => { st with
    messages := initMsgs ++ ⟨nonHintMsgs.toPArray'⟩
  }

  let scope ← getScope
  let env ← getEnv

  modifyCurLevel fun level => pure {level with
    module := env.header.mainModule
    goal := sig,
    scope := scope,
    descrText := match descr with
    | none => ""
    | some s => s.getString
    descrFormat := match statementName with
    | none => "example " ++ (toString <| reprint sig.raw) ++ " := by"
    | some name => (Format.join ["lemma ", reprint name.raw, " ", reprint sig.raw, " := by"]).pretty 10  -- "lemma "  ++ (toString <| reprint name.raw) ++ " " ++ (Format.pretty (reprint sig.raw) 40) ++ " := by"
    hints := hints
  } -- Format.pretty <| format thmStatement.raw }



/-! # Hints -/

syntax hintArg := atomic(" (" (&"strict" <|> &"hidden") " := " withoutPosition(term) ")")

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
elab "Hint" args:hintArg* msg:interpolatedStr(term) : tactic => do
  let mut strict := false
  let mut hidden := false

  -- remove spaces at the beginngng of new lines
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

/-- This tactic allows us to execute an alternative sequence of tactics, but without affecting the
proof state. We use it to define Hints for alternative proof methods or dead ends. -/
elab "Branch" t:tacticSeq : tactic => do
  let b ← saveState
  Tactic.evalTactic t

  -- Show an info whether the branch proofs all remaining goals.
  let gs ← Tactic.getUnsolvedGoals
  if gs.isEmpty then
    logInfo "This branch finishes the proof."
  else
    logInfo "This branch leaves open goals."

  let msgs ← Core.getMessageLog
  b.restore
  Core.setMessageLog msgs



/-! # Make Game -/

def GameLevel.getInventory (level : GameLevel) : InventoryType → InventoryInfo
| .Tactic => level.tactics
| .Definition => level.definitions
| .Lemma => level.lemmas

def GameLevel.setComputedInventory (level : GameLevel) :
    InventoryType → Array ComputedInventoryItem → GameLevel
| .Tactic, v =>     {level with tactics     := {level.tactics     with computed := v}}
| .Definition, v => {level with definitions := {level.definitions with computed := v}}
| .Lemma, v =>      {level with lemmas      := {level.lemmas      with computed := v}}

/-- Build the game. This command will precompute various things about the game, such as which
tactics are available in each level etc. -/
elab "MakeGame" : command => do
  let game ← getCurGame

  -- Check for loops in world graph
  if game.worlds.hasLoops then
    throwError "World graph must not contain loops! Check your `Path` declarations."

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

    -- Basic inventory item availability: all locked.
    let Availability₀ : HashMap Name ComputedInventoryItem :=
      HashMap.ofList $
        ← allItems.toList.mapM fun item => do
          let data := (← getInventoryDoc? item inventoryType).get!
          return (item, {
            name := item
            displayName := data.displayName
            category := data.category
            locked := true })

    -- Availability after a given world
    let mut itemsInWorld : HashMap Name (HashMap Name ComputedInventoryItem) := {}
    for (worldId, _) in game.worlds.nodes.toArray do
      let mut items := Availability₀
      let predecessors := game.worlds.predecessors worldId
      for predWorldId in predecessors do
        for item in newItemsInWorld.find! predWorldId do
          let data := (← getInventoryDoc? item inventoryType).get!
          items := items.insert item {
            name := item
            displayName := data.displayName
            category := data.category
            locked := false }
      itemsInWorld := itemsInWorld.insert worldId items

    for (worldId, world) in game.worlds.nodes.toArray do
      let mut items := itemsInWorld.find! worldId

      let levels := world.levels.toArray.insertionSort fun a b => a.1 < b.1

      for (levelId, level) in levels do
        let levelInfo := level.getInventory inventoryType

        -- add items in `levelInfo.new` permanently as unlocked
        for item in levelInfo.new do
          let data := (← getInventoryDoc? item inventoryType).get!
          items := items.insert item {
            name := item
            displayName := data.displayName
            category := data.category
            locked := false }

        let itemsArray := items.toArray
          |>.insertionSort (fun a b => a.1.toString < b.1.toString)
          |>.map (·.2)
          |>.map (fun item => { item with
            -- if `levelInfo.only` is set, disable everything not in there,
            -- otherwise disable all in `levelInfo.disabled`
            disabled := if levelInfo.only.size == 0 then
              levelInfo.disabled.contains item.name
            else
              not (levelInfo.only.contains item.name)
            })

        modifyLevel ⟨← getCurGameId, worldId, levelId⟩ fun level => do
          return level.setComputedInventory inventoryType itemsArray



/-! # Debugging tools -/

-- /-- Print current game for debugging purposes. -/
-- elab "PrintCurGame" : command => do
--   logInfo (toJson (← getCurGame))

/-- Print current level for debugging purposes. -/
elab "PrintCurLevel" : command => do
  logInfo (repr (← getCurLevel))

/-- Print levels for debugging purposes. -/
elab "PrintLevels" : command => do
  logInfo $ repr $ (← getCurWorld).levels.toArray
