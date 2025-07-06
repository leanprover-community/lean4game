import Lean
import GameServer.RpcHandlers
import Lean.Server.FileWorker
open Lean.Lsp

set_option linter.unusedVariables false

namespace GameServer

open Lean

def createDebugNotification (msg : String) : JsonRpc.Message :=
  let params : Json.Structured := .arr #[msg] -- TODO: didn't know how to create a `.obj`
  .notification "lean4game/debug" params

/--
Send debug messages as `lean4game/debug` RPC notification.

Can be used to print debug messages from within `GameServer` to the server console.

Currently they are ignored by the frontend, but in dev mode they
appear as `DEBUG:` message in the server's shell (see `relay/index.mjs`)
-/
def _root_.debug_msg (msg : String) : IO Unit := do
  let o ← IO.getStdout
  o.writeLspMessage (createDebugNotification msg)

def parseParams (paramType : Type) [FromJson paramType] (params : Json) : IO paramType :=
match fromJson? params with
| Except.ok parsed => pure parsed
| Except.error inner => panic! s!"Got param with wrong structure: {params.compress}\n{inner}"

inductive JsonKey where
| mandatory (k : String)
| optional (k : String)
| allInArray

instance : Coe String JsonKey := ⟨JsonKey.mandatory⟩
instance : ToString JsonKey := ⟨fun k => match k with | .mandatory s => s | .optional s => "?" ++ s | .allInArray => "*"⟩

#check Lean.RBMap.contains

def modifyJson {α : Type} [FromJson α] [ToJson α] (p : Json) (key : List JsonKey) (mod : α → α) : IO Json := do
  match key with
  | [] => match fromJson? p with
    | .ok v => return toJson (mod v)
    | .error e => throw (IO.userError e)
  | .mandatory k :: ks =>
    match p.getObjVal? k with
    | .ok v => return p.setObjVal! k (← modifyJson v ks mod)
    | .error e => throw (IO.userError s!"[GameServer] (key: {key}): {e}")
  | .optional k :: ks =>
    match p.getObj? with
    | .ok v =>
      if (v.find compare k).isSome then
        match p.getObjVal? k with
        | .ok v => return p.setObjVal! k (← modifyJson v ks mod)
        | .error e => throw (IO.userError s!"[GameServer] (key: {key}): {e}")
      else return p
    | .error e => throw (IO.userError s!"[GameServer] (key: {key}): {e}")
  | .allInArray :: ks =>
    match p.getArr? with
    | .ok v => return Json.arr (← Array.mapM (modifyJson · ks mod) v)
    | .error e => throw (IO.userError s!"[GameServer] (key: {key}): {e}")


def toStructured (p : Json) : IO Json.Structured := do
  let .ok params := Json.toStructured? p
    | panic! "[GameServer] Cannot convert to Structured"
  return params

/-- Redirect message from the client to the Lean server. -/
def forwardMessage (msg : JsonRpc.Message) : IO JsonRpc.Message := do
  -- let game ← GameServer.getCurGame
  match msg with
    | .notification "initialized" params? =>
      return msg
    | .notification method@("textDocument/didOpen") none =>
      debug_msg s!"BUG: I thought receiving 'textDocument/didOpen' without params was impossible"
      IO.Process.exit 2
    | .notification method@("textDocument/didOpen") (some params') =>
      let mut params : Json := ToJson.toJson params'
      let textDocument := params.getObjValD "textDocument"
      let .ok content := textDocument.getObjValAs? String "text"
        | panic! s!"[GameServer]: ERROR: received didOpen notification with invalid parameters!"
      let .ok uri := textDocument.getObjValAs? String "uri"
        | panic! s!"[GameServer]: ERROR: received didOpen notification with invalid parameters!"

      -- URI example: `file:///mygame/DemoWorld1/L_1.lean`
      -- TODO: is this also true on Windows?

      -- let levelId := getLevelIdFromUri game uri
      -- debug_msg s!"[GameServer] `didOpen` {levelId}"
      -- let some level ← getLevel? levelId
      --   | panic! "[GameServer] Level not found"

      let template := s!"import Game.Levels.DemoWorld.L01_HelloWorld import GameServer.RpcHandlers example (h : x = 2) (g: y = 4) : x + x = y := by\n{content}\ndone"

      params := params.setObjVal! "textDocument" (textDocument.setObjVal! "text" template)
      let .ok paramsStructured := Json.toStructured? params
        | panic! "[GameServer] unhandled"

      return .notification method paramsStructured
    -- textDocument/didChange

    | .notification method@("textDocument/didChange") (some params) =>
      let params : Json := ToJson.toJson params
      -- let params ← modifyJson params ["params","contentChanges", .allInArray, "range", "start", "line"] (· + 1)
      -- let params ← modifyJson params ["params","contentChanges", .allInArray, "range", "end", "line"] (· + 1)
      return .notification method (← toStructured params)

    | .request id method@("$/lean/rpc/call") params? => do
      let some params := params?
        | panic! "[GameServer] unhandled"
      let params := toJson params
      match params.getObjValAs? String "method" with
      | .error e => panic! s!"[GameServer] Missing method in rpc call: {e}"
      | .ok "Lean.Widget.getInteractiveTermGoal"
      | .ok "Game.getInteractiveGoals"
      | .ok "Game.getProofState" => do
        -- let params ← modifyJson params ["params","position", "line"] (· + 1)
        -- let params ← modifyJson params ["position", "line"] (· + 1)
        return .request id method (some (← toStructured params))
      | .ok "Lean.Widget.getWidgets" => do
        -- let params ← modifyJson params ["params", "line"] (· + 1)
        -- let params ← modifyJson params ["position", "line"] (· + 1)
        return .request id method (some (← toStructured params))
      | .ok "Lean.Widget.getInteractiveDiagnostics" => do
        -- let params ← modifyJson params ["params", .optional "lineRange", "start"] (· + 1)
        -- let params ← modifyJson params ["params", .optional "lineRange", "end"] (· + 1)
        -- let params ← modifyJson params ["position", "line"] (· + 1)
        return .request id method (some (← toStructured params))
      | .ok _ => return .request id method params?

    | .request id method params? =>
      -- debug_msg s!"TODO client request {method} not implemented!"

      /-
      monaco requests to modify:

      * textDocument/didOpen: params.textDocument.text
      * textDocument/codeAction: params.range
      * textDocument/semanticTokens/range: params.range
      * textDocument/didChange: params.contentChanges
      * textDocument/completion: params.position
      * textDocument/hover: params.position
      * textDocument/documentHighlight: params.position
      * ...
      * $/lean/rpc/call
        * Lean.Widget.getInteractiveGoals: params.position
        * Lean.Widget.getInteractiveTermGoal: params.position
        * Lean.Widget.getWidgets: params.position
        * Lean.Widget.getInteractiveDiagnostics: params.lineRange, params.position
        * ...
      -/
      return msg
    | .notification method params? =>
      -- debug_msg s!"TODO client notification {method} not implemented!"
      return msg
    | .response id result =>
      return msg
    | .responseError id code message data? =>
      return msg

/-- Redirect message from the Lean server back to the client. -/
def returnMessage (msg : JsonRpc.Message) : IO JsonRpc.Message := do
  -- let game ← GameServer.getCurGame
  match msg with
    | .request id method params? =>
      debug_msg s!"TODO server request {method} not implemented!"
      return msg
    | .notification method params? =>
      debug_msg s!"TODO server notification {method} not implemented!"
      return msg
    | .response id result =>
      return msg
    | .responseError id code message data? =>
      return msg
