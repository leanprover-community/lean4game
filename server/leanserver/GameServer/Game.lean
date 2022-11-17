import Lean

namespace Game
open Lean
open Server
open Watchdog
open Lsp
open JsonRpc

partial def handleServerEvent (ev : ServerEvent) : ServerM Bool := do
  match ev with
  | ServerEvent.clientMsg msg =>
    match msg with
    | Message.request id "info" _ =>
      (← read).hOut.writeLspResponse {
        id := id
        result := "Hello"
      }
      return true
    | _ => return false
  | _ => return false

end Game
