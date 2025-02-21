import GameServer.Command
import GameServer.Tactic

-- import GameServer.RpcHandlers -- only needed to collect the translations of "level completed" msgs

/-!
# Frontend

This is the file which needs to be imported by any Lean project which defines a game.

In particular it provides the necessary commands like `MakeGame`, which needs to be called
at the very end of Lean project (bottom of default target).
-/
