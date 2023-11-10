import Lean.Server.Watchdog

open Lean
open Server
open Watchdog
open Lsp
open IO
open JsonRpc

#check  JsonRpc.Request

@[export game_send_message]
def sendMessage (s : String) : IO Unit := do
  let expectedMethod := "initialize"
  let j ← ofExcept (Json.parse s)
  let m  ← match fromJson? j with
  | Except.ok (m : JsonRpc.Message) => pure m
  | Except.error inner => throw $ userError s!"JSON '{j.compress}' did not have the format of a JSON-RPC message.\n{inner}"
  let initRequest ← match m with
    | Message.request id method params? =>
      if method = expectedMethod then
        let j := toJson params?
        match fromJson? j with
        | Except.ok v => pure $ JsonRpc.Request.mk id expectedMethod (v : InitializeParams)
        | Except.error inner => throw $ userError s!"Unexpected param '{j.compress}' for method '{expectedMethod}'\n{inner}"
      else
        throw $ userError s!"Expected method '{expectedMethod}', got method '{method}'"
    | _ => throw $ userError s!"Expected JSON-RPC request, got: '{(toJson m).compress}'"
  IO.println s!"{initRequest.param.editDelay}"
  return ()
