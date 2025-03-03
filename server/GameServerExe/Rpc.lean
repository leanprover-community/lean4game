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

private def rpcTest (_ : Lsp.PlainGoalParams) : RequestM (RequestTask String) := do
  return RequestTask.pure "Test RPC answer."

builtin_initialize
  registerBuiltinRpcProcedure
    `Game.test
    Lsp.PlainGoalParams
    String
    rpcTest
