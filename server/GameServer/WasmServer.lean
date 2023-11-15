import Lean.Server.Watchdog
import GameServer.Game

namespace WasmServer.Watchdog
open Lean
open Server
open Watchdog
open IO
open Lsp
open JsonRpc
open System.Uri

def counter := IO.mkRef 0


def readLspRequestAs (s : String) (expectedMethod : String) (α : Type) [FromJson α] : IO (Request α) := do
  let j ← ofExcept (Json.parse s)
  let m  ← match fromJson? j with
  | Except.ok (m : JsonRpc.Message) => pure m
  | Except.error inner => throw $ userError s!"JSON '{j.compress}' did not have the format of a JSON-RPC message.\n{inner}"
  let initRequest ← match m with
    | Message.request id method params? =>
      if method = expectedMethod then
        let j := toJson params?
        match fromJson? j with
        | Except.ok v => pure $ JsonRpc.Request.mk id expectedMethod (v : α)
        | Except.error inner => throw $ userError s!"Unexpected param '{j.compress}' for method '{expectedMethod}'\n{inner}"
      else
        throw $ userError s!"Expected method '{expectedMethod}', got method '{method}'"
    | _ => throw $ userError s!"Expected JSON-RPC request, got: '{(toJson m).compress}'"


@[export game_send_message]
def sendMessage (s : String) : IO Unit := do
  -- IO.println s!"received {s}"
  -- if args.length < 2 then
  --   throwServerError s!"Expected 1-3 command line arguments in addition to `--server`:
  --     game directory, the name of the main module (optional), and the name of the game (optional)."
  -- let gameDir := args[1]!
  -- let module := if args.length < 3 then defaultGameModule else args[2]!
  -- let gameName := if args.length < 4 then defaultGameName else args[3]!
  -- let workerPath := "./gameserver"
  -- -- TODO: Do the following commands slow us down?
  -- let srcSearchPath ← initSrcSearchPath (← getBuildDir)
  -- let references ← IO.mkRef (← loadReferences)
  -- let fileWorkersRef ← IO.mkRef (RBMap.empty : FileWorkerMap)
  -- -- let i ← maybeTee "wdIn.txt" false i
  -- -- let o ← maybeTee "wdOut.txt" true o
  -- -- let e ← maybeTee "wdErr.txt" true e
  -- let state : GameServerState := {
  --   env := ← importModules #[] {} 0 --← createEnv gameDir module,
  --   game := "TEST",
  --   gameDir := "test",
  --   inventory := #[]
  --   difficulty := 0
  --   }
  let initRequest ← readLspRequestAs s "initialize" InitializeParams

  -- We misuse the `rootUri` field to the gameName
  let rootUri? := "TEST"
  let initRequest := {initRequest with param := {initRequest.param with rootUri?}}
  let o ← IO.getStdout
  o.writeLspResponse {
    id     := initRequest.id
    result := {
      capabilities := mkLeanServerCapabilities
      serverInfo?  := some {
        name     := "Lean 4 Game Server"
        version? := "0.1.1"
      }
      : InitializeResult
    }
  }
  -- let context : ServerContext := {
  --   hIn            := i
  --   hOut           := o
  --   hLog           := e
  --   args           := args
  --   fileWorkersRef := fileWorkersRef
  --   initParams     := initRequest.param
  --   workerPath
  --   srcSearchPath
  --   references
  -- }
  -- discard $ ReaderT.run (StateT.run initAndRunWatchdogAux state) context

  return ()
