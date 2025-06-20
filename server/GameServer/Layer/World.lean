import GameServer.Layer.Level
import GameServer.Lean.HashMap

/-! ## World -/

namespace GameServer

open Lean

/-- A world is a collection of levels, like a chapter. -/
structure World where
  /- Internal name of the world. Not visible to the player. -/
  name: Name
  /-- Display title of the world. -/
  title: String := default
  /-- World introduction to be shown before the first level is loaded. (markdown) -/
  introduction: String := default
  /-- TODO: This is currently unused. -/
  conclusion : String := default
  /-- The levels of the world. -/
  levels: Std.HashMap Nat GameServer.Level := default
  /-- The introduction image of the world. -/
  image: String := default
deriving Inhabited

instance : ToJson World := ⟨
  fun world => Json.mkObj [
    ("name", toJson world.name),
    ("title", world.title),
    ("introduction", world.introduction),
    ("image", world.image)]
⟩

def World.merge (old : World) (new : World) : World :=
  { new with
    levels := old.levels.merge new.levels GameServer.Level.merge}
