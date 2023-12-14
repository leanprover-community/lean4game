import GameServer.RpcHandlers

open Lean

structure GameServerState :=
(env : Lean.Environment)
(game : Name)
(gameDir : String)
(inventory : Array String)
(difficulty : Nat)

abbrev GameServerM := StateT GameServerState Server.Watchdog.ServerM

instance : MonadEnv GameServerM := {
  getEnv := do return (← get).env
  modifyEnv := fun f => do
    let s ← get
    set {s with env := f s.env}
}

namespace Game
open Server
open Watchdog
open Lsp
open JsonRpc
open IO

structure SetInventoryParams where
  inventory : Array String
  difficulty : Nat
deriving ToJson, FromJson

partial def handleServerEvent (ev : ServerEvent) : GameServerM Bool := do
  match ev with
  | ServerEvent.clientMsg msg =>
    match msg with
    | Message.notification "$/game/setInventory" params =>
      let p := (← parseParams SetInventoryParams (toJson params))
      let s ← get
      set {s with inventory := p.inventory, difficulty := p.difficulty}
      let st ← read
      let workers ← st.fileWorkersRef.get
      for (_, fw) in workers do
        fw.stdin.writeLspMessage msg

      return true
    | _ => return false
  | _ => return false

end Game
