import GameServer.Inventory.Basic

/-!
-/

namespace GameServer

open Lean

/-- The extension that stores the doc templates. Note that you can only add, but never modify
entries! -/
initialize inventoryTemplateExt :
    SimplePersistentEnvExtension InventoryTemplate (Array InventoryTemplate) ←
  registerSimplePersistentEnvExtension {
    name := `inventory_keys
    addEntryFn := Array.push
    addImportedFn := Array.flatMap id }

/-- Receive the template with that matches `(name, type)` -/
def getInventoryTemplate? [Monad m] [MonadEnv m] (n : Name) (type : InventoryType) :
    m (Option InventoryTemplate) := do
  return (inventoryTemplateExt.getState (← getEnv)).find? (fun x => x.name == n && x.type == type)

/-- The extension that contains the inventory content after it has been processed.
`MakeGame` is the only command adding items here. -/
initialize inventoryExt : SimplePersistentEnvExtension InventoryItem (Array InventoryItem) ←
  registerSimplePersistentEnvExtension {
    name := `inventory_doc
    addEntryFn := Array.push
    addImportedFn := Array.flatMap id }

/-- Receive the item with that matches `(name, type)` -/
def getInventoryItem? [Monad m] [MonadEnv m] (n : Name) (type : InventoryType) :
    m (Option InventoryItem) := do
  return (inventoryExt.getState (← getEnv)).find? (fun x => x.name == n && x.type == type)
