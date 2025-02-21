import GameServerExe.RpcHandlers

open Lean

structure GameServerState where
  env : Lean.Environment
  game : Name
  gameDir : String
  inventory : Array String
  difficulty : Nat

abbrev GameServerM := StateT GameServerState Server.Watchdog.ServerM

instance : MonadEnv GameServerM := {
  getEnv := do return (← get).env
  modifyEnv := fun f => do
    let s ← get
    set {s with env := f s.env}
}

namespace Game
open Server
open Watchdog
open Lsp
open JsonRpc
open IO

/- Game-specific version of `InitializeParams` that allows for extra options: -/

structure InitializationOptions extends Lean.Lsp.InitializationOptions where
  difficulty : Nat
  inventory : Array String
  deriving ToJson, FromJson

structure InitializeParams where
  processId? : Option Int := none
  clientInfo? : Option ClientInfo := none
  /- We don't support the deprecated rootPath
  (rootPath? : Option String) -/
  rootUri? : Option String := none
  initializationOptions? : Option InitializationOptions := none
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

def InitializeParams.toLeanInternal (p : InitializeParams) : Lean.Lsp.InitializeParams :=
{
  processId? := p.processId?
  clientInfo? := p.clientInfo?
  rootUri? := p.rootUri?
  initializationOptions? := p.initializationOptions?.map fun o => {
    editDelay? := o.editDelay?
    hasWidgets? := o.hasWidgets?
  }
  capabilities := p.capabilities
  trace := p.trace
  workspaceFolders? := p.workspaceFolders?
}

end Game
