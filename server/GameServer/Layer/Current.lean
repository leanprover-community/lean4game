import Lean
import GameServer.Layer.Defs

namespace GameServer

open Lean

/-!
## Environment extensions for game specification
-/

variable {m: Type → Type} [Monad m] [MonadEnv m]

/-- Register a (non-persistent) environment extension to hold the current game -/
initialize curGameExt : EnvExtension (Option Name) ← registerEnvExtension (pure none)

/-- Register a (non-persistent) environment extension to hold the current world -/
initialize curWorldExt : EnvExtension (Option Name) ← registerEnvExtension (pure none)

/-- Register a (non-persistent) environment extension to hold the current level -/
initialize curLevelExt : EnvExtension (Option Nat) ← registerEnvExtension (pure none)

/-- Set the current game -/
def setCurGameId (game : Name) : m Unit :=
  modifyEnv (curGameExt.setState · game)

/-- Set the current world -/
def setCurWorldId (world : Name) : m Unit :=
  modifyEnv (curWorldExt.setState · world)

/-- Set the current level -/
def setCurLevelIdx (level : Nat) : m Unit :=
  modifyEnv (curLevelExt.setState · level)

/-- Get the current layer. -/
def getCurLayer [MonadError m] : m Layer := do
  -- previously, we also had `curGameExt.getState (← getEnv), ` in here, which got removed
  -- when we made the `Game` command optional
  match curWorldExt.getState (← getEnv), curLevelExt.getState (← getEnv) with
  | some _, some _ => return Layer.Level
  | some _, none => return Layer.World
  | none, none => return Layer.Game
  | _, _ => throwError "Invalid Layer"

/-- Get the current game, or default if none is specified -/
def getCurGameId [Monad m] : m Name := do
  match curGameExt.getState (← getEnv) with
  | some game => return game
  | none => return .mkSimple defaultGameName

/-- Get the current world -/
def getCurWorldId [MonadError m] : m Name := do
  match curWorldExt.getState (← getEnv) with
  | some world => return world
  | none => throwError "Current world not set"

/-- Get the current level -/
def getCurLevelIdx [MonadError m] : m Nat := do
  match curLevelExt.getState (← getEnv) with
  | some level => return level
  | none => throwError "Current level not set"
