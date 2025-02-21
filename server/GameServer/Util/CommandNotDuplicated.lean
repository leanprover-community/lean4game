import Lean

namespace GameServer

open Lean Elab Command

def checkCommandNotDuplicated (items : Array Name) (cmd := "Command") : CommandElabM Unit := do
  if ¬ items.isEmpty then
    logWarning <| s!"You should only use one `{cmd}` per level, " ++
      "but it can take multiple arguments: `{cmd} obj₁ obj₂ obj₃`!"
