import GameServer.Tactic
import GameServer.Command

#eval do
  Lean.logWarning <| "`import GameServer.Commands` is deprecated! " ++
    "Please replace it with `import GameServer`!"

-- import GameServer.RpcHandlers -- only needed to collect the translations of "level completed" msgs
