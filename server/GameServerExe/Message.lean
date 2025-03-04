import Lean

-- TODO: The only reason we import `Commands` is so that it gets built to on `lake build`
-- should we have a different solution?

set_option linter.unusedVariables false

namespace GameServer

open Lean

/-- Redirect message from the client to the Lean server. -/
def forwardMessage (msg : JsonRpc.Message) : JsonRpc.Message := Id.run do
  match msg with
    | .request id method params? =>
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
      return msg
    | .response id result =>
      return msg
    | .responseError id code message data? =>
      return msg

/-- Redirect message from the Lean server back to the client. -/
def returnMessage (msg : JsonRpc.Message) : JsonRpc.Message := Id.run do
  match msg with
    | .request id method params? =>
      return msg
    | .notification method params? =>
      return msg
    | .response id result =>
      return msg
    | .responseError id code message data? =>
      return msg

def createDebugNotification (msg : String) : JsonRpc.Message :=
  let params : Json.Structured := .arr #[msg] -- TODO: didn't know how to create a `.obj`
  .notification "lean4game/debug" params

/--
Send debug messages as `lean4game/debug` RPC notification.

Can be used to print debug messages from within `GameServerExe` to the server console.

Currently they are ignored by the frontend, but in dev mode they
appear as `DEBUG:` message in the server's shell (see `relay/index.mjs`)
-/
def _root_.debug_msg (msg : String) : IO Unit := do
  let o ← IO.getStdout
  o.writeLspMessage (createDebugNotification msg)
