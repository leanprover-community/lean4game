import GameServer.SaveData
import GameServer.Inventory
import GameServer.Lean.PrettyPrinter
import GameServer.Options
import GameServer.Helpers

namespace GameServer

open Lean Elab Command

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
      | none => pure ""
    | template =>
      -- TODO: Process content template.
      -- TODO: Add information about inventory items
      pure $ template.replace "[[mathlib_doc]]"
        s!"[mathlib doc](https://leanprover-community.github.io/mathlib4_docs/find/?pattern={name}#doc)"

    match item.type with
    | .Theorem =>
      modifyEnv (inventoryExt.addEntry · { item with
        content := content
        -- Add the theorem statement to the doc
        statement := (← getStatementString name)
      })
    | _ =>
      modifyEnv (inventoryExt.addEntry · { item with
        content := content
      })

  -- For each `worldId` this contains a set of items used in this world
  let mut usedItemsInWorld : Std.HashMap Name (Std.HashSet Name) := {}

  -- For each `worldId` this contains a set of items newly defined in this world
  let mut newItemsInWorld : Std.HashMap Name (Std.HashSet Name) := {}

  -- Items that should not be displayed in inventory
  let mut hiddenItems : Std.HashSet Name := {}

  let allWorlds := game.worlds.nodes.toArray
  let nrWorlds := allWorlds.size
  let mut nrLevels := 0

  -- Calculate which "items" are used/new in which world
  for (worldId, world) in allWorlds do
    let mut usedItems : Std.HashSet Name := {}
    let mut newItems : Std.HashSet Name := {}
    for inventoryType in #[.Tactic, .Definition, .Theorem] do
      for (levelId, level) in world.levels.toArray do
        usedItems := usedItems.insertMany (level.getInventory inventoryType).used
        newItems := newItems.insertMany (level.getInventory inventoryType).new
        hiddenItems := hiddenItems.insertMany (level.getInventory inventoryType).hidden

        -- if the previous level was named, we need to add it as a new theorem
        if inventoryType == .Theorem then
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

          if inventoryType == .Theorem then

      -- if the last level was named, we need to add it as a new theorem
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
  let mut worldsWithNewItem : Std.HashMap Name (Std.HashSet Name) := {}
  for (worldId, _world) in allWorlds do
    for newItem in newItemsInWorld.getD worldId {} do
      worldsWithNewItem := worldsWithNewItem.insert newItem $
        (worldsWithNewItem.getD newItem {}).insert worldId

  -- For each `worldId` this is a HashSet of `worldId`s that this world depends on.
  let mut worldDependsOnWorlds : Std.HashMap Name (Std.HashSet Name) := {}

  -- For a pair of `worldId`s `(id₁, id₂)` this is a HasSet of "items" why `id₁` depends on `id₂`.
  let mut dependencyReasons : Std.HashMap (Name × Name) (Std.HashSet Name) := {}

  -- Calculate world dependency graph `game.worlds`
  for (dependentWorldId, _dependentWorld) in allWorlds do
    let mut dependsOnWorlds : Std.HashSet Name := {}
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
      pure {game with worlds := {game.worlds with edges := ∅}}

    for (dependentWorldId, worldIds) in worldDependsOnWorlds.toArray do
      modifyCurGame fun game =>
        pure {game with worlds := {game.worlds with
          edges := game.worlds.edges.insertMany (worldIds.toArray.map fun wid => (wid, dependentWorldId))}}

  -- Add the number of levels and worlds to the tile for the landing page
  modifyCurGame fun game => pure {game with tile := {game.tile with
    levels := nrLevels
    worlds := nrWorlds }}

  -- Apparently we need to reload `game` to get the changes to `game.worlds` we just made
  let game ← getCurGame

  let mut allItemsByType : Std.HashMap InventoryType (Std.HashSet Name) := {}
  -- Compute which inventory items are available in which level:
  for inventoryType in #[.Tactic, .Definition, .Theorem] do

    -- Which items are introduced in which world?
    let mut theoremStatements : Std.HashMap (Name × Nat) Name := {}
    -- TODO: I believe `newItemsInWorld` has way to many elements in it which we iterate over
    -- e.g. we iterate over `ring` for `Theorem`s as well, but so far that seems to cause no problems
    let mut allItems : Std.HashSet Name := {}
    for (worldId, world) in game.worlds.nodes.toArray do
      let mut newItems : Std.HashSet Name := {}
      for (levelId, level) in world.levels.toArray do
        let newTheorems := (level.getInventory inventoryType).new
        newItems := newItems.insertMany newTheorems
        allItems := allItems.insertMany newTheorems
        if inventoryType == .Theorem then
          -- For levels `2, 3, …` we check if the previous level was named
          -- in which case we add it as available theorem.
          match levelId with
          | 0 => pure ()
          | 1 => pure () -- level ids start with 1, so we need to skip 1, too.
          | i₀ + 1 =>
            -- add named statement from previous level to the available theorems.
            let some idx := world.levels.get? (i₀) | throwError s!"Level {i₀ + 1} not found for world {worldId}!"
            match (idx).statementName with
            | .anonymous => pure ()
            | .num _ _ => panic "Did not expect to get a numerical statement name!"
            | .str pre s =>
              let name := Name.str pre s
              newItems := newItems.insert name
              allItems := allItems.insert name
              theoremStatements := theoremStatements.insert (worldId, levelId) name
      if inventoryType == .Theorem then
        -- if named, add the theorem from the last level of the world to the inventory
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
    let Availability₀ : Std.HashMap Name InventoryTile :=
      Std.HashMap.ofList $
        ← allItems.toList.mapM fun item => do
          -- Using a match statement because the error message of `Option.get!` is not helpful.
          match (← getInventoryItem? item inventoryType) with
          | none =>
            -- Note: we did have a panic here before because theorem statement and doc entry
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
    let mut itemsInWorld : Std.HashMap Name (Std.HashMap Name InventoryTile) := {}
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
        if inventoryType == .Theorem then
          match theoremStatements.get? (worldId, levelId) with
          | none => pure ()
          | some name =>
            let data := (← getInventoryItem? name inventoryType).get!
            items := items.insert name {
              name := name
              displayName := data.displayName
              category := data.category
              world := worldId
              -- from the previous level. This is fine b/c in practise levels start at 1
              level := (levelId - 1 : Nat)
              proven := true
              altTitle := data.statement
              locked := false }

        -- add marks for `disabled` and `new` theorems here, so that they only apply to
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
    theorems := (← getTiles .Theorem).map (fun tile => {tile with hidden := hiddenItems.contains tile.name})
    tactics := (← getTiles .Tactic).map (fun tile => {tile with hidden := hiddenItems.contains tile.name})
    definitions := (← getTiles .Definition).map (fun tile => {tile with hidden := hiddenItems.contains tile.name})
    theoremTab := none
  }

  saveGameData allItemsByType inventory
