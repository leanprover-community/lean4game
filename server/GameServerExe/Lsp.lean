import Lean.Data.Lsp.InitShutdown

namespace GameServer.Lsp

open Lean Lsp

/-- Game-specific version of `InitializationOptions` that allows for extra options: -/
structure InitializationOptions extends Lean.Lsp.InitializationOptions where
  difficulty : Nat
  inventory : Array String
  deriving ToJson, FromJson

/-- Copy of `Lean.Lsp.InitializeParams` with custom `InitializationOptions`. -/
-- @[inherit_doc Lean.Lsp.InitializeParams]
structure InitializeParams  where
  processId? : Option Int := none
  clientInfo? : Option ClientInfo := none
  /- We don't support the deprecated rootPath
  (rootPath? : Option String) -/
  rootUri? : Option String := none
  initializationOptions? : Option GameServer.Lsp.InitializationOptions := none
  capabilities : ClientCapabilities
  /-- If omitted, we default to off. -/
  trace : Trace := Trace.off
  workspaceFolders? : Option (Array WorkspaceFolder) := none
  deriving ToJson

instance : FromJson InitializeParams where
  fromJson? j := do
    let processId? := j.getObjValAs? Int "processId"
    let clientInfo? := j.getObjValAs? ClientInfo "clientInfo"
    let rootUri? := j.getObjValAs? String "rootUri"
    let initializationOptions? := j.getObjValAs? InitializationOptions "initializationOptions"
    let capabilities ← j.getObjValAs? ClientCapabilities "capabilities"
    let trace := (j.getObjValAs? Trace "trace").toOption.getD Trace.off
    let workspaceFolders? := j.getObjValAs? (Array WorkspaceFolder) "workspaceFolders"
    return ⟨
      processId?.toOption,
      clientInfo?.toOption,
      rootUri?.toOption,
      initializationOptions?.toOption,
      capabilities,
      trace,
      workspaceFolders?.toOption⟩

def InitializeParams.toLeanInternal (params : InitializeParams) : Lean.Lsp.InitializeParams :=
  { params with
    initializationOptions? := params.initializationOptions?.map fun options => { options with }}
