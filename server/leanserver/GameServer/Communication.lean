/- Inspired by `Lean/Data/Lsp/Communication.lean` -/
import Lean.Data.JsonRpc

/-! Reading/writing Game Server Protocol messages from/to IO handles. -/

namespace IO.FS.Stream

open Lean
open Lean.JsonRpc

section

def readJsonLine (h : FS.Stream) : IO Json := do
  let s ← h.getLine
  ofExcept (Json.parse s)

def readGspMessage (h : FS.Stream) : IO Message := do
  let j ← h.readJsonLine
  match fromJson? j with
  | Except.ok m => pure m
  | Except.error inner =>
    throw $
      userError s!"JSON '{j.compress}' did not have the format of a JSON-RPC message.\n{inner}"

def readGspRequestAs (h : FS.Stream) (expectedMethod : String) (α) [FromJson α]
    : IO (Request α) := do
  let m ← h.readGspMessage
  match m with
  | Message.request id method params? =>
    if method = expectedMethod then
      let j := toJson params?
      match fromJson? j with
      | Except.ok v => pure ⟨id, expectedMethod, v⟩
      | Except.error inner =>
        throw $
          userError s!"Unexpected param '{j.compress}' for method '{expectedMethod}'\n{inner}"
    else
      throw $ userError s!"Expected method '{expectedMethod}', got method '{method}'"
  | _ => throw $ userError s!"Expected JSON-RPC request, got: '{(toJson m).compress}'"

def readGspNotificationAs
    (h : FS.Stream) (nBytes : Nat) (expectedMethod : String) (α) [FromJson α]
    : IO (Notification α) := do
  let m ← h.readMessage nBytes
  match m with
  | Message.notification method params? =>
    if method = expectedMethod then
      let j := toJson params?
      match fromJson? j with
      | Except.ok v => pure ⟨expectedMethod, v⟩
      | Except.error inner =>
        throw $
          userError s!"Unexpected param '{j.compress}' for method '{expectedMethod}'\n{inner}"
    else
      throw $ userError s!"Expected method '{expectedMethod}', got method '{method}'"
  | _ => throw $ userError s!"Expected JSON-RPC notification, got: '{(toJson m).compress}'"

def readGspResponseAs
    (h : FS.Stream) (nBytes : Nat) (expectedID : RequestID) (α) [FromJson α]
    : IO (Response α) := do
  let m ← h.readMessage nBytes
  match m with
  | Message.response id result =>
    if id == expectedID then
      match fromJson? result with
      | Except.ok v => pure ⟨expectedID, v⟩
      | Except.error inner => throw $ userError s!"Unexpected result '{result.compress}'\n{inner}"
    else
      throw $ userError s!"Expected id {expectedID}, got id {id}"
  | Message.notification .. => readResponseAs h nBytes expectedID α
  | _ => throw $ userError s!"Expected JSON-RPC response, got: '{(toJson m).compress}'"

end

section
  variable [ToJson α]

  def writeGspMessage (h : FS.Stream) (m : Message) : IO Unit := do
    h.putStr ((toJson m).compress ++ "\n")
    h.flush

  def writeGspRequest (h : FS.Stream) (r : Request α) : IO Unit :=
    h.writeGspMessage r

  def writeGspNotification (h : FS.Stream) (n : Notification α) : IO Unit :=
    h.writeGspMessage n

  def writeGspResponse (h : FS.Stream) (r : Response α) : IO Unit :=
    h.writeGspMessage r

  def writeGspResponseError (h : FS.Stream) (e : ResponseError Unit) : IO Unit :=
    h.writeGspMessage (Message.responseError e.id e.code e.message none)

  def writeGspResponseErrorWithData (h : FS.Stream) (e : ResponseError α) : IO Unit :=
    h.writeGspMessage e
end

end IO.FS.Stream
