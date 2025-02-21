import GameServerExe.Rpc.GetProofState
import GameServerExe.Rpc.GetInteractiveGoals

open GameServer Widget
open Lean Server

builtin_initialize
  registerBuiltinRpcProcedure
    `Game.getInteractiveGoals
    Lsp.PlainGoalParams
    (Option <| InteractiveGoals
    )
    getInteractiveGoals

builtin_initialize
  registerBuiltinRpcProcedure
    `Game.getProofState
    Lsp.PlainGoalParams
    (Option ProofState)
    getProofState
