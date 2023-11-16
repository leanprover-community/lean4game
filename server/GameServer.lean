import Lean.Server.Watchdog
import GameServer.Commands
import GameServer.Game

Game "TestGame"
Title "Hello Test"

MakeGame

#eval do
  let env ← (Lean.getEnv : Lean.MetaM _)
  return  (gameExt.getState env).size
