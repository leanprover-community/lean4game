import Lean

open Lean

/-- A persistent environment extension that is meant to hold a single (mutable) value. -/
def SingleValPersistentEnvExtension (α : Type) := PersistentEnvExtension α α α 

instance {α} [Inhabited α] : Inhabited (SingleValPersistentEnvExtension α) :=
  inferInstanceAs <| Inhabited  <| PersistentEnvExtension α α α

def registerSingleValPersistentEnvExtension (name : Name) (α : Type) [Inhabited α] : IO (SingleValPersistentEnvExtension α) := 
  registerPersistentEnvExtension {
    name            := name,
    mkInitial       := pure default,
    addImportedFn   := mkStateFromImportedEntries (fun _ b => return b) (return default),
    addEntryFn      := (λ _ b => b),
    exportEntriesFn := λ x => #[x]
  }

variable {m: Type → Type} [Monad m] [MonadEnv m] {α : Type} [Inhabited α] 

def SingleValPersistentEnvExtension.get (ext : SingleValPersistentEnvExtension α) : m α :=
  return ext.getState (← getEnv)

def SingleValPersistentEnvExtension.set (ext : SingleValPersistentEnvExtension α) (a : α) : m Unit := do
  modifyEnv (ext.modifyState · (λ _ => a))