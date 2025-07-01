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

/--
Takes the JSON of an element of `contentChanges` in the rpc notif. `textDocument/didChange`
and applies the `shift` to all ranges.
-/
def shiftRange (shift : Nat → Nat) (change : Json) : Json := Id.run do
  let mut range := change.getObjValD "range"
  let mut start := range.getObjValD "start"
  let mut «end» := range.getObjValD "end"
  let .ok startLine := start.getObjValAs? Nat "line"
    | panic! "[GameServer] unhandled"
  let .ok endLine := end.getObjValAs? Nat "line"
    | panic! "[GameServer] unhandled"
  start := start.setObjValAs! "line" (shift startLine)
  «end» := «end».setObjValAs! "line" (shift endLine)
  range := range.setObjVal! "start" start
  range := range.setObjVal! "end" «end»
  change.setObjVal! "range" range

def parseParams (paramType : Type) [FromJson paramType] (params : Json) : IO paramType :=
match fromJson? params with
| Except.ok parsed => pure parsed
| Except.error inner => panic! s!"Got param with wrong structure: {params.compress}\n{inner}"


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

      let template := s!"import GameServer.RpcHandlers example (h : x = 2) (g: y = 4) : x + x = y := by\n{content}\ndone"

      params := params.setObjVal! "textDocument" (textDocument.setObjVal! "text" template)
      let .ok paramsStructured := Json.toStructured? params
        | panic! "[GameServer] unhandled"

      return .notification method paramsStructured
    -- textDocument/didChange

    | .notification method@("textDocument/didChange") (some params') =>
      let mut params : Json := ToJson.toJson params'
      let textDocument := params.getObjValD "textDocument"
      let .ok contentChanges := (params.getObjValD "contentChanges").getArr?
        | panic! "[GameServer] unhandled"

      let contentChangeNew : Json := .arr <| contentChanges.map (shiftRange (·+1))

      params := params.setObjVal! "contentChanges" contentChangeNew
      let .ok paramsStructured := Json.toStructured? params
        | panic! "[GameServer] unhandled"
      debug_msg s!"{params}"
      return .notification method paramsStructured


    | .request id method@("$/lean/rpc/call") params? =>
      let some params := params?
        | panic! "[GameServer] unhandled"
      let params : RpcCallParams ← parseParams RpcCallParams (toJson params)
      debug_msg s!"Method: {params.method} {params.method == `Game.getInteractiveGoals}"
      if params.method == `Game.getInteractiveGoals || params.method == `Game.getProofState then
        let p := params.params
        let p : TextDocumentPositionParams ← parseParams TextDocumentPositionParams (toJson p)
        let p : TextDocumentPositionParams := {p with position := {p.position with line := p.position.line + 1}}
        let params := {params with params := toJson p, position := {params.position with line := params.position.line + 1}}
        let .ok params := Json.toStructured? params
          | panic! "[GameServer] unhandled"
        return .request id method (some params)
      else
        return .request id method params?

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
