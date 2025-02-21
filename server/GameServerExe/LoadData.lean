import GameServer.Config.SaveData
import GameServer.EnvExtensions
import I18n

namespace GameServer

open Lean GameData

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
