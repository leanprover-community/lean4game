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


syntax hintArg := " (" (&"strict" <|> &"hidden") " := " withoutPosition(term) ")"

/-- A tactic that can be used inside `Statement`s to indicate in which proof states players should
see hints. The tactic does not affect the goal state. -/
elab "Hint" args:hintArg* msg:interpolatedStr(term) : tactic => do

  let mut strict := false
  let mut hidden := false

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
      return ← mkLambdaFVars #[vars] $ ← elabTermAndSynthesize text none
    let textmvar ← mkFreshExprMVar none
    guard $ ← isDefEq textmvar text -- Store the text in a mvar.
    -- The information about the hint is logged as a message using `logInfo` to transfer it to the
    -- `Statement` command defined below:
    logInfo $
      .tagged `Hint $
      .nest (if strict then 1 else 0) $
      .nest (if hidden then 1 else 0) $
      .compose (.ofGoal textmvar.mvarId!) (.ofGoal goal)

/-- Define the statement of the current level.

Arguments:
- ident: (Optional) The name of the statemtent.
- descr: The human-readable version of the lemma as string. Accepts Markdown and Mathjax.
-/
elab "Statement" statementName:ident ? descr:str sig:declSig val:declVal : command => do

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
    descrText := descr.getString,
    descrFormat := match statementName with
    | none => "example " ++ (toString <| reprint sig.raw) ++ " := by"
    | some name => (Format.join ["lemma ", reprint name.raw, " ", reprint sig.raw, " := by"]).pretty 10  -- "lemma "  ++ (toString <| reprint name.raw) ++ " " ++ (Format.pretty (reprint sig.raw) 40) ++ " := by"
    hints := hints
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

/-- From a term `s` and a list of pairs `(i, t) ; Ident × Term`, create the syntax
where `s` is preceded with universal quantifiers `∀ i : t`. -/
def mkGoalSyntax (s : Term) : List (Ident × Term) → MacroM Term
| (n, t)::tail => do return (← `(∀ $n : $t, $(← mkGoalSyntax s tail)))
| [] => return s

-- def elabHint (hidden : Bool) (binders : TSyntaxArray `Lean.Parser.Term.bracketedBinder)
--   (goal : TSyntax `term) (msg : TSyntax `interpolatedStrKind) :=
-- liftTermElabM do withOptions (fun options => options.setBool `linter.unusedVariables false) do
--   let (g, decls) ← elabBinders binders fun xs => do
--     let g ← mkForallFVars xs $ ← elabTermAndSynthesize goal none
--     synthesizeSyntheticMVarsNoPostponing false
--     return (← instantiateMVars g, ← xs.mapM (fun x => x.fvarId!.getDecl))
--   let varsName := `vars
--   let msg ← withLocalDeclD varsName (mkApp (mkConst ``Array [levelZero]) (mkConst ``Expr)) fun vars => do
--     let mut msg ← `(m! $msg)
--     for i in [:decls.size] do
--       msg ← `(let $(mkIdent decls[i]!.userName) := $(mkIdent varsName)[$(quote i)]!; $msg)
--     return ← mkLambdaFVars #[vars] $ ← elabTermAndSynthesize msg none

--   if g.hasMVar then throwError m!"Goal contains metavariables: {g}"

  -- modifyCurLevel fun level => pure {level with hints := level.hints.push {
  --   goal := g,
  --   intros := decls.size,
  --   hidden := hidden,
  --   text := msg }}

/-- Declare a hint. This version doesn't prevent the unused linter variable from running. -/
local elab "Hint'" binders:bracketedBinder* ":" goal:term "=>" msg:interpolatedStr(term) : command =>
  -- elabHint false binders goal msg
  pure ()

/--
Declare a hint. This version doesn't prevent the unused linter variable from running.
A hidden hint is only displayed if explicitly requested by the user.
-/
local elab "HiddenHint'" binders:bracketedBinder* ":" goal:term "=>" msg:interpolatedStr(term) : command => do
  -- elabHint true binders goal msg
  pure ()

/-- Declare a hint in reaction to a given tactic state in the current level. -/
macro "Hint" decls:bracketedBinder* ":" goal:term "=>" msg:interpolatedStr(term) : command => do
  `(set_option linter.unusedVariables false in Hint' $decls* : $goal => $msg)

/-- Declare a hidden hint in reaction to a given tactic state in the current level. -/
macro "HiddenHint" decls:bracketedBinder* ":" goal:term "=>" msg:interpolatedStr(term) : command => do
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
elab "NewTactic" args:ident* : command => do
  let names := args.map (·.getId)
  for name in names do checkInventoryDoc .Tactic name
  modifyCurLevel fun level => pure {level with tactics := {level.tactics with new := names}}

/-- Declare tactics that are temporarily disabled in this level -/
elab "DisabledTactic" args:ident* : command => do
  let names := args.map (·.getId)
  -- for name in names do checkInventoryDoc .Tactic name
  modifyCurLevel fun level => pure {level with tactics := {level.tactics with disabled := names}}

/-- Temporarily disable all tactics except the ones declared here -/
elab "OnlyTactic" args:ident* : command => do
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
elab "NewDefinition" args:ident* : command => do
  let names := args.map (·.getId)
  for name in names do checkInventoryDoc .Definition name
  modifyCurLevel fun level => pure {level with definitions := {level.definitions with new := names}}

/-- Declare definitions that are temporarily disabled in this level -/
elab "DisabledDefinition" args:ident* : command => do
  let names := args.map (·.getId)
  -- for name in names do checkInventoryDoc .Definition name
  modifyCurLevel fun level => pure {level with definitions := {level.definitions with disabled := names}}

/-- Temporarily disable all definitions except the ones declared here -/
elab "OnlyDefinition" args:ident* : command => do
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
elab "NewLemma" args:ident* : command => do
  let names := args.map (·.getId)
  for name in names do checkInventoryDoc .Lemma name
  modifyCurLevel fun level => pure {level with lemmas := {level.lemmas with new := names}}

/-- Declare lemmas that are temporarily disabled in this level -/
elab "DisabledLemma" args:ident* : command => do
  let names := args.map (·.getId)
  -- for name in names do checkInventoryDoc .Lemma name
  modifyCurLevel fun level => pure {level with lemmas := {level.lemmas with disabled := names}}

/-- Temporarily disable all lemmas except the ones declared here -/
elab "OnlyLemma" args:ident* : command => do
  let names := args.map (·.getId)
  for name in names do checkInventoryDoc .Lemma name
  modifyCurLevel fun level => pure {level with lemmas := {level.lemmas with only := names}}

/-! ## Make Game -/

def GameLevel.getInventory (level : GameLevel) : InventoryType → InventoryInfo
| .Tactic => level.tactics
| .Definition => level.definitions
| .Lemma => level.lemmas

def GameLevel.setComputedInventory (level : GameLevel) : InventoryType → Array ComputedInventoryItem → GameLevel
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
    let Availability₀ : HashMap Name ComputedInventoryItem :=
      HashMap.ofList $
        ← allItems.toList.mapM fun name => do
          return (name, {
            name
            category := (← getInventoryDoc? name inventoryType).get!.category
            locked := true
            disabled := false})

    -- Availability after a given world
    let mut itemsInWorld : HashMap Name (HashMap Name ComputedInventoryItem) := {}
    for (worldId, _) in game.worlds.nodes.toArray do
      let mut items := Availability₀
      let predecessors := game.worlds.predecessors worldId
      for predWorldId in predecessors do
        for item in newItemsInWorld.find! predWorldId do
          items := items.insert item {
            name := item
            category := (← getInventoryDoc? item inventoryType).get!.category
            locked := false
            disabled := false
          }
      itemsInWorld := itemsInWorld.insert worldId items

    for (worldId, world) in game.worlds.nodes.toArray do
      let mut items := itemsInWorld.find! worldId

      let levels := world.levels.toArray.insertionSort fun a b => a.1 < b.1

      for (levelId, level) in levels do
        for item in (level.getInventory inventoryType).new do
          let category := (← getInventoryDoc? item inventoryType).get!.category
          items := items.insert item {name := item, category, locked := false, disabled := false}
        for item in (level.getInventory inventoryType).disabled do
          let category := (← getInventoryDoc? item inventoryType).get!.category
          items := items.insert item {name := item, category, locked := false, disabled := true}

        let itemsArray := items.toArray
          |>.insertionSort (fun a b => a.1.toString < b.1.toString)
          |>.map (·.2)

        modifyLevel ⟨← getCurGameId, worldId, levelId⟩ fun level => do
          return level.setComputedInventory inventoryType itemsArray
