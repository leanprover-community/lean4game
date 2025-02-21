import GameServer.Inventory.Basic

/-!
Used in `GameServer.SaveData` and `GameServer.Backend.LoadData`.
-/

namespace GameServer

open Lean

namespace GameData

def gameDataPath : System.FilePath := ".lake" / "gamedata"

def gameFileName := s!"game.json"

set_option linter.unusedVariables false in

def docFileName := fun (inventoryType : InventoryType) (name : Name) => s!"doc__{name}.json"

def levelFileName := fun (worldId : Name) (levelId : Nat) => s!"level__{worldId}__{levelId}.json"

def inventoryFileName := s!"inventory.json"

end GameData
