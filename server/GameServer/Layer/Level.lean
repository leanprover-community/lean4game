import Lean
import GameServer.Layer.Current
import GameServer.Inventory.Extension
import GameServer.Tactic.Hint.Defs

/-! ## Levels -/

namespace GameServer

open Lean

structure LevelId where
  game : Name
  world : Name
  level : Nat
deriving Inhabited

instance : ToString LevelId := ⟨fun id =>
  s!"{id.game}:{id.world}:{id.level}"⟩

variable {m: Type → Type} [Monad m] [MonadEnv m]

def getCurLevelId [MonadError m] : m LevelId := do
  return { game := ← getCurGameId, world := ← getCurWorldId, level := ← getCurLevelIdx}

/-- Instance to make GameServer.Level Repr work -/
instance : Repr Elab.Command.Scope := ⟨fun s _ => repr s.currNamespace⟩

structure Level where
  index: Nat
  /-- The title of the level. -/
  title: String := ""
  /-- Introduction text shown all the time. (markdown) -/
  introduction: String := ""
  conclusion: String := ""
  /-- The name of the exercise proven. If provided this theorem will be available in
  future levels. -/
  statementName: Name := default
  hints: Array GoalHintEntry := default
  /-- The statement in Lean. -/
  goal : TSyntax `Lean.Parser.Command.declSig := default
  scope : Elab.Command.Scope := default
  /-- The mathematical statement in mathematician-readable form. (markdown) -/
  descrText: Option String := none
  descrFormat : String := default
  /-- The `category` of theorems to be open by default -/
  theoremTab: Option String := none
  /-- The module to be imported when playing this level -/
  module : Name := default
  tactics: InventoryInfo := default
  definitions: InventoryInfo := default
  theorems: InventoryInfo := default
  /-- A proof template that is printed in an empty editor. -/
  template: Option String := none
  /-- The image for this level. -/
  image : String := default
  /-- A sequence of tactics the game automatically executes before the first step. -/
  preamble : TSyntax `Lean.Parser.Tactic.tacticSeq := default
deriving Inhabited, Repr

/--
Merge two levels.

Currently overwrites old one with the new one
-/
def Level.merge (_old : GameServer.Level) (new : GameServer.Level) : GameServer.Level :=
  new

/-- Json-encodable version of `GameServer.Level`
Fields:
- description: Theorem in mathematical language.
- descriptionGoal: Theorem printed as Lean-Code.
-/
structure LevelInfo where
  index : Nat
  title : String
  tactics : Array InventoryTile
  theorems : Array InventoryTile
  definitions : Array InventoryTile
  introduction : String
  conclusion : String
  descrText : Option String := none
  descrFormat : String := ""
  theoremTab : Option String
  module : Name
  displayName : Option String
  statementName : Option String
  template : Option String
  image: Option String
deriving ToJson, FromJson

def Level.toInfo (lvl : GameServer.Level) (env : Environment) : LevelInfo :=
  { index := lvl.index,
    title := lvl.title,
    tactics := lvl.tactics.tiles,
    theorems := lvl.theorems.tiles,
    definitions := lvl.definitions.tiles,
    descrText := lvl.descrText,
    descrFormat := lvl.descrFormat --toExpr <| format (lvl.goal.raw) --toString <| Syntax.formatStx (lvl.goal.raw) --Syntax.formatStx (lvl.goal.raw) , -- TODO
    introduction := lvl.introduction
    conclusion := lvl.conclusion
    theoremTab := match lvl.theoremTab with
    | some tab => tab
    | none =>
      -- Try to set the theorem tab to the category of the first added theorem
      match lvl.theorems.tiles.find? (·.new) with
      | some tile => tile.category
      | none => none
    statementName := lvl.statementName.toString
    module := lvl.module
    displayName := match lvl.statementName with
      | .anonymous => none
      | name => match (inventoryExt.getState env).find?
          (fun x => x.name == name && x.type == .Theorem) with
        | some n => n.displayName
        | none => name.toString
        -- Note: we could call `.find!` because we check in `Statement` that the
        -- theorem doc must exist.
    template := lvl.template
    image := lvl.image
  }
