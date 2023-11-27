import Lean.Server.Watchdog
import GameServer.FileWorker
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

open MyServer.FileWorker

structure WasmFileState :=
  fileWorkerState : FileWorker.WorkerState
  gameWorkerState : GameWorkerState
  headerTask : Task (Except Error (Snapshots.Snapshot × SearchPath))

structure WasmServerState :=
  initParams? : Option InitializeParams
  gameServerState : GameServerState
  fileState : HashMap String WasmFileState := {}

def wasmSearchPath : SearchPath  := ["/lib", "/gamelib"]

@[export game_make_state]
unsafe def makeState : IO WasmServerState := do
  let e ← IO.getStderr
  try
    Lean.enableInitializersExecution
    searchPathRef.set wasmSearchPath
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
    return ⟨none, state, {}⟩
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

def mkServerContext (state : WasmServerState) : IO ServerContext := do
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
    initParams
    workerPath
    srcSearchPath
    references
  }

def runGameServerM (state : WasmServerState) (x : GameServerM α) : IO (α × WasmServerState) := do
  let (res, gameServerState) ← ReaderT.run
      (StateT.run x state.gameServerState)
      (← mkServerContext state)
  return (res, {state with gameServerState})

def mkWorkerContext (state : WasmServerState) (headerTask : Task (Except Error (Snapshots.Snapshot × SearchPath))) :
    IO FileWorker.WorkerContext := do
  let i ← IO.getStdin
  let o ← IO.getStdout
  let e ← IO.getStderr
  let some initParams := state.initParams?
    | throwServerError "no yet initialized"
  let clientHasWidgets := initParams.initializationOptions?.bind (·.hasWidgets?) |>.getD false
  return {
    hIn  := i
    hOut := o
    hLog := e
    headerTask := headerTask
    initParams := initParams
    clientHasWidgets
  }

def runGameWorkerM (state : WasmServerState) (fileState : WasmFileState) (x : GameWorkerM α) :
    IO (α × WasmFileState) := do
  let s := fileState.fileWorkerState
  let ctx ← mkWorkerContext state fileState.headerTask
  let ((res, gameWorkerState), s) ← StateRefT'.run (s := s) <| ReaderT.run (r := ctx) <|
      StateT.run (s := fileState.gameWorkerState) <| x
  let fileState := {fileState with gameWorkerState := gameWorkerState, fileWorkerState := s}
  return (res, fileState)

def parseParams {paramType : Type} [FromJson paramType] (params : Json) : IO paramType :=
  match fromJson? params with
  | Except.ok parsed => pure parsed
  | Except.error inner => throwServerError s!"Got param with wrong structure: {params.compress}\n{inner}"

def requestWorkerUri (method : String) (params : Json) : IO (Option DocumentUri) := do
  if method == "$/lean/rpc/connect" then
    let ps : Lsp.RpcConnectParams ← parseParams params
    pure <| fileSource ps
  else match (← routeLspRequest method params) with
    | Except.error e =>
      throwServerError e.message
    | Except.ok uri => pure uri

open FileWorker in
def handleDidOpen (params : DidOpenTextDocumentParams) (state : WasmServerState) : IO WasmServerState := do
  let some initParams := state.initParams?
    | throwServerError "no yet initialized"
  let (_, state) ← runGameServerM state do
    let some lvl ← GameServer.getLevelByFileName? initParams
        ((System.Uri.fileUriToPath? params.textDocument.uri).getD params.textDocument.uri |>.toString)
      | throwServerError s!"Level not found: {params.textDocument.uri} | {initParams.rootUri?}"

    let env ← importModules #[
      { module := lvl.module : Import }
    ] {} 0

    (← getStderr).putStr "Import for level completed"

    let doc := params.textDocument
    let meta : DocumentMeta := ⟨doc.uri, doc.version, doc.text.toFileMap, .always⟩
    let clientHasWidgets := initParams.initializationOptions?.bind (·.hasWidgets?) |>.getD false

    let (headerStx, headerTask) ← mkHeaderTask meta (← getStdout) wasmSearchPath env {} clientHasWidgets
    let cancelTk ← CancelToken.new

    let levelParams := {
      uri := meta.uri
      gameDir := state.gameServerState.gameDir
      levelModule := lvl.module
      tactics := lvl.tactics.tiles
      lemmas := lvl.lemmas.tiles
      definitions := lvl.definitions.tiles
      inventory := state.gameServerState.inventory
      difficulty := state.gameServerState.difficulty
      statementName := lvl.statementName
      : Game.DidOpenLevelParams
    }

    let ctx ← mkWorkerContext state headerTask
    let cmdSnaps ← EIO.mapTask (t := headerTask) (match · with
      | Except.ok (s, _) => unfoldSnaps meta #[s] cancelTk levelParams ctx (startAfterMs := 0)
      | Except.error e   => throw (e : ElabTaskError))
    let doc : EditableDocument := { meta, cmdSnaps := AsyncList.delayed cmdSnaps, cancelTk }


    let s : WasmFileState := {
      fileWorkerState := {
        doc             := doc
        initHeaderStx   := headerStx
        pendingRequests := RBMap.empty
        rpcSessions     := RBMap.empty
      }
      gameWorkerState := { levelParams }
      headerTask
    }
    let fileState := state.fileState.insert params.textDocument.uri s
    return {state with fileState}
  return state

@[export game_send_message]
unsafe def sendMessage (s : String) (state : WasmServerState) : IO WasmServerState := do
  let e ← IO.getStderr
  try
    let m ← readMessage s
    match m with
    | Message.request id "initialize" (some params) =>
      let p : InitializeParams ← parseParams (toJson params)
      initializeServer id
      let p := {p with rootUri? := some (toString state.gameServerState.game)}
      return {state with initParams? := some p}
    | _ =>
      let (isGameEv, state) ← runGameServerM state (Game.handleServerEvent (.clientMsg m))
      if isGameEv then
        return state
      else
        match m with
        | Message.notification method (some params) =>
            let handle := (fun α [FromJson α] (handler : α → WasmServerState → IO WasmServerState)
              => parseParams (toJson params) >>= (handler · state))
            match method with --TODO
            | "textDocument/didOpen"            => handle DidOpenTextDocumentParams handleDidOpen
            -- | "textDocument/didChange"          => handle DidChangeTextDocumentParams handleDidChange
            -- | "textDocument/didClose"           => handle DidCloseTextDocumentParams handleDidClose
            -- | "workspace/didChangeWatchedFiles" => handle DidChangeWatchedFilesParams handleDidChangeWatchedFiles
            -- | "$/cancelRequest"                 => handle CancelParams handleCancelRequest
            -- | "$/lean/rpc/connect"              => handle RpcConnectParams (forwardNotification method)
            -- | "$/lean/rpc/release"              => handle RpcReleaseParams (forwardNotification method)
            -- | "$/lean/rpc/keepAlive"            => handle RpcKeepAliveParams (forwardNotification method)
            | _ => return state
        | Message.request id method (some params) =>
          let some uri ← requestWorkerUri method (toJson params)
            | throwServerError s!"Could not find Uri for request: {method}"
          let some fileState := state.fileState.find? uri
            | throwServerError s!"File not open: {uri}"
          let (_, fileState) ← runGameWorkerM state fileState do
            MyServer.FileWorker.mainLoop1 m
          let fileState := state.fileState.insert uri fileState
          return {state with fileState}
        | Message.responseError _ _ e .. =>
          throwServerError s!"Unhandled response error: {e}"
        | _ => throwServerError "Got invalid JSON-RPC message"
        -- match m with
        -- | _ =>
        --   e.putStrLn s!"Expected JSON-RPC request, got: '{(toJson m).compress}'"
        --   return state
  catch err =>
    e.putStrLn s!"Server error: {err}"
    return state
