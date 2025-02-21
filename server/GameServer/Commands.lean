import GameServer.Frontend

#eval do
  Lean.logWarning <| "`import GameServer.Commands` is deprecated! " ++
    "Please replace it with `import GameServer.Frontend`!"

-- import GameServer.RpcHandlers -- only needed to collect the translations of "level completed" msgs
