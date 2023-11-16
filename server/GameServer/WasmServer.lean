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

def ServerState := GameServerState

@[export game_make_state]
unsafe def makeState : IO (ServerState) := do
  let e ← IO.getStderr
  try
    Lean.enableInitializersExecution
    searchPathRef.set ["/lib", "/gamelib"]
    e.putStrLn s!"Importing"
    let state : GameServerState := {
      env := ← importModules #[
          { module := `Init : Import },
          { module := `GameServer : Import }
        ] {} 0 --← createEnv gameDir module,
      game := "TEST",
      gameDir := "test",
      inventory := #[]
      difficulty := 0
    }
    e.putStrLn s!"Import complete"
    let pExtDescrs ← persistentEnvExtensionsRef.get
    pExtDescrs.forM fun extDescr => do
      e.putStrLn ("extension '" ++ toString extDescr.name ++ "'")
      let s := extDescr.toEnvExtension.getState state.env
      let fmt := extDescr.statsFn s.state
      unless fmt.isNil do IO.println ("  " ++ toString (Format.nest 2 (extDescr.statsFn s.state)))
      e.putStrLn ("  number of imported entries: " ++ toString (s.importedEntries.foldl (fun sum es => sum + es.size) 0))
    e.putStrLn s!"{(gameExt.getState state.env).size}"
    let some game := (gameExt.getState state.env).find? `TestGame
      | throwServerError "Game not found"
    let gameJson : Json := toJson game
    -- Add world sizes to Json object
    -- let worldSize := game.worlds.nodes.toList.map (fun (n, w) => (n.toString, w.levels.size))
    -- let gameJson := gameJson.mergeObj (Json.mkObj [("worldSize", Json.mkObj worldSize)])
    e.putStrLn s!"{gameJson}"
    return state
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


@[export game_send_message]
unsafe def sendMessage (s : String) (state : ServerState) : IO Unit := do
  let o ← IO.getStdout
  let e ← IO.getStderr
  try
    let m ← readMessage s
    match m with
    | Message.request id "initialize" params? =>
      initializeServer id
    | Message.request id "info" _ =>

      let some game := (gameExt.getState state.env).find? `TestGame
        | throwServerError "Game not found"
      let gameJson : Json := toJson game
      -- Add world sizes to Json object
      -- let worldSize := game.worlds.nodes.toList.map (fun (n, w) => (n.toString, w.levels.size))
      -- let gameJson := gameJson.mergeObj (Json.mkObj [("worldSize", Json.mkObj worldSize)])
      e.putStrLn s!"{gameJson}"
      o.writeLspResponse ⟨id, gameJson⟩
    | _ => pure () --throw $ userError s!"Expected JSON-RPC request, got: '{(toJson m).compress}'"

  catch err =>
    e.putStrLn s!"Server error: {err}"
    return ()
