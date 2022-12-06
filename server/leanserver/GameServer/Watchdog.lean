/- This file is mostly copied from `Lean/Server/Watchdog.lean`. -/
import Lean
import GameServer.Game

namespace MyServer.Watchdog
open Lean
open Server
open Watchdog
open IO
open Lsp
open JsonRpc
open System.Uri

  partial def mainLoop (clientTask : Task ServerEvent) : GameServerM Unit := do
    let st ← read
    let workers ← st.fileWorkersRef.get
    let mut workerTasks := #[]
    for (_, fw) in workers do
      if let WorkerState.running := fw.state then
        workerTasks := workerTasks.push <| fw.commTask.map (ServerEvent.workerEvent fw)

    let ev ← IO.waitAny (clientTask :: workerTasks.toList)

    if ← Game.handleServerEvent ev then -- handle Game requests
      mainLoop (←runClientTask)
    else
      match ev with
      | ServerEvent.clientMsg msg =>
        match msg with
        | Message.request id "shutdown" _ =>
          shutdown
          st.hOut.writeLspResponse ⟨id, Json.null⟩
        | Message.request id method (some params) =>
          handleRequest id method (toJson params)
          mainLoop (←runClientTask)
        | Message.response .. =>
          -- TODO: handle client responses
          mainLoop (←runClientTask)
        | Message.responseError _ _ e .. =>
          throwServerError s!"Unhandled response error: {e}"
        | Message.notification method (some params) =>
          handleNotification method (toJson params)
          mainLoop (←runClientTask)
        | _ => throwServerError "Got invalid JSON-RPC message"
      | ServerEvent.clientError e => throw e
      | ServerEvent.workerEvent fw ev =>
        match ev with
        | WorkerEvent.ioError e =>
          throwServerError s!"IO error while processing events for {fw.doc.uri}: {e}"
        | WorkerEvent.crashed _ =>
          handleCrash fw.doc.uri #[]
          mainLoop clientTask
        | WorkerEvent.terminated =>
          throwServerError "Internal server error: got termination event for worker that should have been removed"
        | .importsChanged =>
          startFileWorker fw.doc
          mainLoop clientTask

def initAndRunWatchdogAux : GameServerM Unit := do
  let st ← read
  try
    discard $ st.hIn.readLspNotificationAs "initialized" InitializedParams
    let clientTask ← runClientTask
    mainLoop clientTask
  catch err =>
    shutdown
    throw err
  /- NOTE(WN): It looks like instead of sending the `exit` notification,
  VSCode just closes the stream. In that case, pretend we got an `exit`. -/
  let Message.notification "exit" none ←
    try st.hIn.readLspMessage
    catch _ => pure (Message.notification "exit" none)
    | throwServerError "Got `shutdown` request, expected an `exit` notification"

def createEnv : IO Environment := do
  let gameDir := "../../../testgame"

  -- Determine search paths of the game project by running `lake env printenv LEAN_PATH`.
  let out ← IO.Process.output
    { cwd := gameDir, cmd := "lake", args := #["env","printenv","LEAN_PATH"] }
  if out.exitCode != 0 then
    throwServerError s!"Error while running Lake: {out.stderr}"

  -- Make the paths relative to the current directory
  let paths : List System.FilePath := System.SearchPath.parse out.stdout.trim
  let currentDir ← IO.currentDir
  let paths := paths.map fun p => currentDir / (gameDir : System.FilePath) / p

  -- Set the search path
  Lean.searchPathRef.set paths

  let gameName := `TestGame
  let env ← importModules [{ module := `Init : Import }, { module := gameName : Import }] {} 0
  return env

def initAndRunWatchdog (args : List String) (i o e : FS.Stream) : IO Unit := do
  let workerPath := "./gameserver"
  -- TODO: Do the following commands slow us down?
  let srcSearchPath ← initSrcSearchPath (← getBuildDir)
  let references ← IO.mkRef (← loadReferences)
  let fileWorkersRef ← IO.mkRef (RBMap.empty : FileWorkerMap)
  let i ← maybeTee "wdIn.txt" false i
  let o ← maybeTee "wdOut.txt" true o
  let e ← maybeTee "wdErr.txt" true e
  let initRequest ← i.readLspRequestAs "initialize" InitializeParams
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
  let state := {env := ← createEnv, game := `TestGame}
  let context : ServerContext := {
    hIn            := i
    hOut           := o
    hLog           := e
    args           := args
    fileWorkersRef := fileWorkersRef
    initParams     := initRequest.param
    workerPath
    srcSearchPath
    references
  }
  discard $ ReaderT.run (StateT.run initAndRunWatchdogAux state) context

def watchdogMain (args : List String) : IO UInt32 := do
  let i ← IO.getStdin
  let o ← IO.getStdout
  let e ← IO.getStderr
  try
    initAndRunWatchdog args i o e
    return 0
  catch err =>
    e.putStrLn s!"Watchdog error: {err}"
    return 1

end MyServer.Watchdog
