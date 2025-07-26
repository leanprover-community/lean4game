import GameServer.EnvExtensions
import I18n

open Lean Meta Elab Command Std

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

namespace GameData
  def gameDataPath : System.FilePath := ".lake" / "gamedata"
  def gameFileName := s!"game.json"
  def docFileName := fun (inventoryType : InventoryType) (name : Name) => s!"doc__{inventoryType}__{name}.json"
  def levelFileName := fun (worldId : Name) (levelId : Nat) => s!"level__{worldId}__{levelId}.json"
  def inventoryFileName := s!"inventory.json"
end GameData

open GameData in
-- TODO: register all of this as ToJson instance?
def saveGameData (allItemsByType : HashMap InventoryType (HashSet Name))
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

  for inventoryType in [InventoryType.Lemma, .Tactic, .Definition] do
    for name in allItemsByType.getD inventoryType {} do
      let some item ← getInventoryItem? name inventoryType
        | throwError "Expected item to exist: {name}"
      IO.FS.writeFile (path / docFileName inventoryType name) (toString (toJson item))

  IO.FS.writeFile (path / inventoryFileName) (toString (toJson inventory))

  -- write file for translation
  I18n.createTemplate

open GameData

def loadData (f : System.FilePath) (α : Type) [FromJson α] : IO α := do
  let str ← IO.FS.readFile f
  let json ← match Json.parse str with
  | .ok v => pure v
  | .error e => throw (IO.userError e)
  let data ← match fromJson? json with
  | .ok v => pure v
  | .error e => throw (IO.userError e)
  return data

def loadGameData (gameDir : System.FilePath) : IO Game :=
  loadData (gameDir / gameDataPath / gameFileName) Game

def loadLevelData (gameDir : System.FilePath) (worldId : Name) (levelId : Nat) : IO LevelInfo :=
  loadData (gameDir / gameDataPath / levelFileName worldId levelId) LevelInfo
