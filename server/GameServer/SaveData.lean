import GameServer.EnvExtensions

open Lean Meta Elab Command


/-! ## Copy images -/

open IO.FS System FilePath in
/-- Copies the folder `images/` to `.lake/gamedata/images/` -/
def copyImages : IO Unit := do
  let target : FilePath := ".lake" / "gamedata"
  if ← FilePath.pathExists "images" then
    for file in ← walkDir "images" do
      let outFile := target.join file
      -- create the directories
      if ← file.isDir then
        createDirAll outFile
      else
        if let some parent := outFile.parent then
          createDirAll parent
        -- copy file
        let content ← readBinFile file
        writeBinFile outFile content


-- TODO: I'm not sure this should be happening here...
#eval IO.FS.createDirAll ".lake/gamedata/"

-- TODO: register all of this as ToJson instance?
def saveGameData (allItemsByType : HashMap InventoryType (HashSet Name))
    (inventory : InventoryOverview): CommandElabM Unit := do
  let game ← getCurGame
  let env ← getEnv
  let path : System.FilePath := s!"{← IO.currentDir}" / ".lake" / "gamedata"

  if ← path.isDir then
    IO.FS.removeDirAll path
  IO.FS.createDirAll path

  -- copy the images folder
  copyImages

  for (worldId, world) in game.worlds.nodes.toArray do
    for (levelId, level) in world.levels.toArray do
      IO.FS.writeFile (path / s!"level__{worldId}__{levelId}.json") (toString (toJson (level.toInfo env)))

  IO.FS.writeFile (path / s!"game.json") (toString (getGameJson game))

  for inventoryType in [InventoryType.Lemma, .Tactic, .Definition] do
    for name in allItemsByType.findD inventoryType {} do
      let some item ← getInventoryItem? name inventoryType
        | throwError "Expected item to exist: {name}"
      IO.FS.writeFile (path / s!"doc__{inventoryType}__{name}.json") (toString (toJson item))

  IO.FS.writeFile (path / s!"inventory.json") (toString (toJson inventory))
