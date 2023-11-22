import Lean.Server.Watchdog
import GameServer.Commands
import GameServer.Game

Game "TestGame"
Title "Hello Test"

World "Test"
Level 1

Statement : 1 = 1 := sorry

MakeGame
