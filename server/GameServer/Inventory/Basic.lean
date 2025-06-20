import Lean

/-! ## Inventory (documentation)

The inventory contains documentation that the user can access.
There are three inventory types: Theorem, Tactic, Definition. They vary about in the information
they carry.

The commands `TheoremDoc`, `TacticDoc`, and `DefinitionDoc` add keys and templates to an
env. extension called `InventoryTemplateExt`. Commands like `NewTheorem`, etc. as well as
`Statement` check if there is a key registered in this extension and might add a default or
print a warning if not.

Then, `MakeGame` takes the templates from `InventoryTemplateExt` and creates the documentation entries
that are sent to the client. This allows us to modify them like adding information from
mathlib or from parsing the theorem in question.
-/

namespace GameServer

open Lean

/-- The game knows three different inventory types that contain slightly different information -/
inductive InventoryType where
  | Tactic
  | Theorem
  | Definition
deriving ToJson, FromJson, Repr, BEq, Hashable, Inhabited

instance : ToString InventoryType where
  toString t := match t with
    | .Tactic => "Tactic"
    | .Theorem => "Theorem"
    | .Definition => "Definition"

/-- The keys/templates of the inventory items, stored in `InventoryTemplateExt`. -/
structure InventoryTemplate where
  /-- Theorem, Tactic, or Definition -/
  type: InventoryType
  /-- Depends on the type:
  * Tactic: the tactic's name
  * Theorem: fully qualified theorem name
  * Definition: no restrictions (preferably the definitions fully qualified name)
  -/
  name: Name
  /-- Only for Theorems. To sort them into tabs -/
  category: String := default
  /-- Free-text short name -/
  displayName: String := name.toString
  /-- Template documentation. Allows for special tags to insert mathlib info [TODO!] -/
  content: String := ""
  deriving ToJson, Repr, Inhabited

/-- A full inventory item including the processing by `MakeGame`, which creates these
from the `InventoryTemplate`s and modifies them. -/
structure InventoryItem extends InventoryTemplate where
  statement: String := ""
  deriving ToJson, Repr, Inhabited

/-- A reduced variant of `InventoryItem` which is used for the tiles in the doc -/
structure InventoryTile where
  /--
  The name of the item. The restrictions are:

  * for Tactics: The name of the tactic.
  * for Theorems: *Fully qualified* theorem name.
  * for Definitions: no restrictions.
  -/
  name : Name
  /-- The display name shown in the inventory. This can be free-text. -/
  displayName : String
  /-- Category to group inventory items by (currently only used for theorems). -/
  category : String
  /-- The world which introduced this item. -/
  world : Option Name := none
  /-- The level which introduced this item. -/
  level : Option Nat := none
  /-- Set to `true` if there exists an exercise in the game proving this statement. -/
  proven := false
  /-- If `true` then the item only gets unlocked in a later level. -/
  locked := true
  /-- If `true` then the item is blocked for this level. -/
  disabled := false
  /-- To mark an item that has been added freshly in this level. -/
  new := false
  /-- hide the item in the inventory display -/
  hidden := false
  /-- hover text -/
  altTitle : String := default
deriving ToJson, FromJson, Repr, Inhabited, BEq

def InventoryItem.toTile (item : InventoryItem) : InventoryTile := {
      name := item.name,
      displayName := item.displayName
      category := item.category
}

structure InventoryInfo where
  /-- inventory items used by the main sample solution of this level -/
  used : Array Name
  /-- new inventory items introduced by this level -/
  new : Array Name
  /-- inventory items that shall not be displayed in the inventory -/
  hidden : Array Name
  /-- inventory items exceptionally forbidden in this level -/
  disabled : Array Name
  /-- only these inventory items are allowed in this level (ignored if empty) -/
  only : Array Name
  /-- inventory items in this level (computed by `MakeGame`) -/
  tiles : Array InventoryTile
deriving ToJson, FromJson, Repr, Inhabited
