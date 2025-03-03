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
