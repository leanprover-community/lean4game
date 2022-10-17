import Lean

open Lean Std

def HashMapExtension (α β : Type) [BEq α] [Hashable α] := SimplePersistentEnvExtension (α × β) (HashMap α β)

instance (α β : Type) [BEq α] [Hashable α] : Inhabited (HashMapExtension α β) :=
  inferInstanceAs (Inhabited (SimplePersistentEnvExtension (α × β) (HashMap α β)))

def mkHashMapExtension (name : Name) (α β : Type) [BEq α] [Hashable α]  : IO (HashMapExtension α β) :=
  registerSimplePersistentEnvExtension {
    name          := name,
    addImportedFn := mkStateFromImportedEntries (λ s n => s.insert n.1 n.2) {},
    addEntryFn    := (λ s n => s.insert n.1 n.2),
    toArrayFn     := fun es => es.toArray
  }

namespace HashMapExtension

variable {α β : Type} [BEq α] [Hashable α] {m: Type → Type} [Monad m] [MonadEnv m]

def find? (ext : HashMapExtension α β) (a : α) : m $ Option β := do
  return (ext.getState (← getEnv)).find? a

def insert (ext : HashMapExtension α β) (a : α) (b : β) : m Unit :=
  modifyEnv (ext.addEntry · (a, b))

def update (ext : HashMapExtension α β) (a : α) (b : β) : m Unit :=
  modifyEnv (ext.addEntry · (a, b))

end HashMapExtension
