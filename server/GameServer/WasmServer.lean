import Lean.Server.Watchdog
import GameServer.EnvExtensions
import GameServer.Game

namespace WasmServer.Watchdog
open Lean
open Server
open Watchdog
open IO
open Lsp
open JsonRpc
open System.Uri

structure WasmServerState :=
  initParams? : Option InitializeParams
  gameServerState : GameServerState

@[export game_make_state]
unsafe def makeState : IO WasmServerState := do
  let e ← IO.getStderr
  try
    Lean.enableInitializersExecution
    searchPathRef.set ["/lib", "/gamelib"]
    let env ← importModules #[
      { module := `GameServer : Import }
    ] {} 0
    let state : GameServerState := {
      env,
      game := `TestGame,
      gameDir := "test",
      inventory := #[]
      difficulty := 0
    }
    return ⟨none, state⟩
  catch err =>
    e.putStrLn s!"Import error: {err}"
    throw err

def readMessage (s : String) : IO JsonRpc.Message := do
  let j ← ofExcept (Json.parse s)
  let m  ← match fromJson? j with
  | Except.ok (m : JsonRpc.Message) => pure m
  | Except.error inner => throw $ userError s!"JSON '{j.compress}' did not have the format of a JSON-RPC message.\n{inner}"
  return m

def readLspRequestAs (s : String) (expectedMethod : String) (α : Type) [FromJson α] : IO (Request α) := do
  let m ← readMessage s
  match m with
  | Message.request id method params? =>
    if method = expectedMethod then
      let j := toJson params?
      match fromJson? j with
      | Except.ok v => pure $ JsonRpc.Request.mk id expectedMethod (v : α)
      | Except.error inner => throw $ userError s!"Unexpected param '{j.compress}' for method '{expectedMethod}'\n{inner}"
    else
      throw $ userError s!"Expected method '{expectedMethod}', got method '{method}'"
  | _ => throw $ userError s!"Expected JSON-RPC request, got: '{(toJson m).compress}'"

def initializeServer (id : RequestID) : IO Unit := do
  let o ← IO.getStdout
  o.writeLspResponse {
    id     := id
    result := {
      capabilities := mkLeanServerCapabilities
      serverInfo?  := some {
        name     := "Lean 4 Game Server"
        version? := "0.1.1"
      }
      : InitializeResult
    }
  }
  return ()

def mkContext (state : WasmServerState) : IO ServerContext := do
  let i ← IO.getStdin
  let o ← IO.getStdout
  let e ← IO.getStderr
  let srcSearchPath ← searchPathRef.get
  let references ← IO.mkRef (← loadReferences)
  let fileWorkersRef ← IO.mkRef (RBMap.empty : FileWorkerMap)
  let workerPath := "no-worker-path"
  let some initParams := state.initParams?
    | throwServerError "no yet initialized"
  return {
    hIn            := i
    hOut           := o
    hLog           := e
    args           := []
    fileWorkersRef := fileWorkersRef
    initParams := {initParams with rootUri? := some (toString state.gameServerState.game)}
    workerPath
    srcSearchPath
    references
  }

def runGameServerM (state : WasmServerState) (x : GameServerM α) : IO (α × WasmServerState) := do
  let (res, gameServerState) ← ReaderT.run
      (StateT.run x state.gameServerState)
      (← mkContext state)
  return (res, {state with gameServerState})

def readParams (params? : Option Json.Structured) [FromJson α] : IO α :=
  let j := toJson params?
  match fromJson? j with
  | Except.ok v => pure v
  | Except.error inner => throw $ userError s!"Unexpected param '{j.compress}' \n{inner}"

@[export game_send_message]
unsafe def sendMessage (s : String) (state : WasmServerState) : IO WasmServerState := do
  let e ← IO.getStderr
  try
    let m ← readMessage s
    match m with
    | Message.request id "initialize" params? =>
      let p : InitializeParams ← readParams params?
      initializeServer id
      return {state with initParams? := some p}
    | Message.notification "textDocument/didOpen" params? =>
      let some initParams := state.initParams?
        | throwServerError "no yet initialized"
      let p : LeanDidOpenTextDocumentParams ← readParams params?
      let (_, state) ← runGameServerM state do
        let some lvl ← GameServer.getLevelByFileName? initParams
            ((System.Uri.fileUriToPath? p.textDocument.uri).getD p.textDocument.uri |>.toString)
          | throwServerError s!"Level not found: {p.textDocument.uri}"
        e.putStrLn s!"{lvl.module}"
      return state
    | _ =>
      let (isGameEv, state) ← runGameServerM state (Game.handleServerEvent (.clientMsg m))
      if isGameEv then
        return state
      else
        match m with
        | _ =>
          e.putStrLn s!"Expected JSON-RPC request, got: '{(toJson m).compress}'"
          return state
  catch err =>
    e.putStrLn s!"Server error: {err}"
    return state
