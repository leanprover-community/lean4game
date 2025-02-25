import GameServer.Config.SaveData
import GameServer.EnvExtensions
import I18n

namespace GameServer

open Lean Meta Elab Command

/-! ## Save data

Compare to `GameServerExe.LoadData`
-/

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

open GameData in
-- TODO: register all of this as ToJson instance?
def saveGameData (allItemsByType : Std.HashMap InventoryType (Std.HashSet Name))
    (inventory : InventoryOverview): CommandElabM Unit := do
  let game ← getCurGame
  let env ← getEnv
  let path := (← IO.currentDir) / gameDataPath

  if ← path.isDir then
    IO.FS.removeDirAll path
  IO.FS.createDirAll path

  -- copy the images folder
  copyImages

  for (worldId, world) in game.worlds.nodes.toArray do
    for (levelId, level) in world.levels.toArray do
      IO.FS.writeFile (path / levelFileName worldId levelId) (toString (toJson (level.toInfo env)))

  IO.FS.writeFile (path / gameFileName) (toString (getGameJson game))

  for inventoryType in [InventoryType.Theorem, .Tactic, .Definition] do
    for name in allItemsByType.getD inventoryType {} do
      let some item ← getInventoryItem? name inventoryType
        | continue -- TODO: cleanup. Hidden items should also not appear in `allItemsByType`
      IO.FS.writeFile (path / docFileName inventoryType name) (toString (toJson item))

  IO.FS.writeFile (path / inventoryFileName) (toString (toJson inventory))

  -- write file for translation
  I18n.createTemplate
