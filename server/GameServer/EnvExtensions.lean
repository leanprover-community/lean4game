import GameServer.Util.AbstractCtx
import GameServer.Util.Graph
import GameServer.Tactic.Hint.Defs
import GameServer.Inventory.Extension
import GameServer.Layer

open GameServer

-- TODO: Is there a better place?
/-- Keywords that the server should not consider as tactics.

Note: Added `clear` tactic because currently it is very useful in combination with
`Branch` and `Hint` (i.e. using `clear` before a `Hint` in order to remove any irrelevant
hypotheses).
-/
def GameServer.ALLOWED_KEYWORDS : List String :=
  ["with", "fun", "at", "only", "by", "generalizing", "if", "then", "else", "clear", "using"]

-- Note: When changing any of these default names, one also needs to change them in `index.mjs`

/-- The default game module name. -/
def defaultGameModule: String := "Game"

/-! # Environment extensions

The game framework stores almost all its game building data in environment extensions
defined in this file.
-/

open Lean

variable {m: Type → Type} [Monad m] [MonadEnv m]

structure InventoryOverview where
  tactics : Array InventoryTile
  theorems : Array InventoryTile
  definitions : Array InventoryTile
  theoremTab : Option String
deriving ToJson, FromJson

-- TODO: Reuse the following code for checking available tactics in user code:
structure UsedInventory where
(tactics : Std.HashSet Name := {})
(definitions : Std.HashSet Name := {})
(theorems : Std.HashSet Name := {})

-- def getIntroducedInventory (game : Game) [MonadError m] : m (Array Name) := do
--   let allItems : Array Name := game.worlds.nodes.fold (fun L _ world => L ++
--     world.levels.fold (fun LL _ level =>
--       LL ++ level.tactics.new ++ level.theorems.new
--     ) #[]) #[]

--   pure allItems
