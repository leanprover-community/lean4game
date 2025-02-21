import GameServer.Layer.Game

/-! ## Game environment extension -/

namespace GameServer

open Lean

initialize gameExt : PersistentEnvExtension (Name × Game) (Name × Game) (Std.HashMap Name Game) ←
  do registerPersistentEnvExtension {
    name          := `gameExt,
    mkInitial     := pure {},
    addImportedFn := fun ess => do
      let mut games := {}
      for es in ess do
        for (name, game) in es do
          match games.get? name with
          | some oldgame =>
            games := games.insert name (Game.merge oldgame game)
          | none =>
            games := games.insert name game
      return games
    addEntryFn    := (λ s n => s.insert n.1 n.2),
    exportEntriesFn := Std.HashMap.toArray,
    statsFn := fun s => format "number of local entries: " ++ format s.size
}

variable {m: Type → Type} [Monad m] [MonadEnv m]

def getGame? (n : Name) : m (Option Game) := do
  return (gameExt.getState (← getEnv)).get? n

def insertGame (n : Name) (g : Game) : m Unit := do
  modifyEnv (gameExt.addEntry · (n, g))

def getLevel? (levelId : LevelId) : m (Option GameServer.Level) := do
  let some game ← getGame? levelId.game
    | return none
  let some world := game.worlds.nodes.get? levelId.world
    | return none
  let some level := world.levels.get? levelId.level
    | return none
  return level

def getCurGame [Monad m] : m Game := do
  let some game ← getGame? (← getCurGameId)
    | let game := {name := .mkSimple defaultGameName}
      insertGame (.mkSimple defaultGameName) game
      return game
  return game

def modifyCurGame (fn : Game → m Game) [MonadError m] : m Unit := do
  let game ← getCurGame
  insertGame game.name (← fn game)

def addWorld (world : World) [MonadError m] : m Unit := do
  modifyCurGame fun game => do
    return {game with worlds := game.worlds.insertNode world.name world}

def getCurWorld [MonadError m] : m World := do
  let some world := (← getCurGame).worlds.nodes.get? (← getCurWorldId)
    | throwError m!"World {← getCurWorldId} does not exist"
  return world

def modifyCurWorld (fn : World → m World) [MonadError m] : m Unit := do
  modifyCurGame fun game => do
    let world ← getCurWorld
    return {game with worlds := {game.worlds with nodes := game.worlds.nodes.insert world.name (← fn world) }}

def addLevel (level : GameServer.Level) [MonadError m] : m Unit := do
  let worldId ← getCurWorldId
  match ← getLevel? ⟨← getCurGameId, worldId, level.index⟩ with
  | some _existingLevel =>
    throwError m!"Level {level.index} already exists for world {worldId}!"
  | none =>
    modifyCurWorld fun world => do
      return {world with levels := world.levels.insert level.index level}

def getCurLevel [MonadError m] : m GameServer.Level := do
  let some level := (← getCurWorld).levels.get? (← getCurLevelIdx)
    | throwError m!"Level {← getCurLevelIdx} does not exist"
  return level

def modifyCurLevel (fn : GameServer.Level → m GameServer.Level) [MonadError m] : m Unit := do
  modifyCurWorld fun world => do
    let level ← getCurLevel
    return {world with levels := world.levels.insert level.index (← fn level)}

def modifyLevel (levelId : LevelId) (fn : GameServer.Level → m GameServer.Level) [MonadError m] : m Unit := do
  let some game ← getGame? levelId.game
    | throwError m!"Game {levelId.game} does not exist"
  let some world := (← getCurGame).worlds.nodes.get? levelId.world
    | throwError m!"World {levelId.world} does not exist"
  let some level := world.levels.get? levelId.level
    | throwError m!"Level {levelId.level} does not exist"
  let level' ← fn level
  let world' := {world with levels := world.levels.insert levelId.level level'}
  let game' := {game with worlds := game.worlds.insertNode levelId.world world'}
  insertGame levelId.game game'
