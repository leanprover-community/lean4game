import GameServer.Layer.World
import GameServer.Util.Graph

/-! ## Game -/

namespace GameServer

open Lean

/-- A tile as they are displayed on the servers landing page. -/
structure GameTile where
  /-- The title of the game -/
  title: String
  /-- One catch phrase about the game -/
  short: String := default
  /-- One paragraph description what the game is about -/
  long: String := default
  /-- List of languages the game supports

  TODO: What's the expectected format
  TODO: Must be a list with a single language currently
   -/
  languages: List String := default
  /-- A list of games which this one builds upon -/
  prerequisites: List String := default
  /-- Number of worlds in the game -/
  worlds: Nat := default
  /-- Number of levels in the game -/
  levels: Nat := default
  /-- A cover image of the game

  TODO: What's the format? -/
  image: String := default
deriving Inhabited, ToJson, FromJson

structure Game where
  /-- Internal name of the game. -/
  name : Name
  /-- TODO: currently unused. -/
  title : String := default
  /-- Text displayed on the main landing page of the game. -/
  introduction : String := default
  /-- Text displayed on the main landing page of the game. -/
  info : String := default
  /-- TODO: currently unused. -/
  conclusion : String := default
  /-- TODO: currently unused. -/
  authors : List String := default
  worlds : Graph Name World := default
  /-- The tile displayed on the server's landing page. -/
  tile : GameTile := default
  /-- The path to the background image of the world. -/
  image : String := default
deriving Inhabited, ToJson, FromJson

-- TODO: rename to `Game.toJson`
def getGameJson (game : Game) : Json := Id.run do
  let gameJson : Json := toJson game
  -- Add world sizes to Json object
  let worldSize := game.worlds.nodes.toList.map (fun (n, w) => (n.toString, w.levels.size))
  let gameJson := gameJson.mergeObj (Json.mkObj [("worldSize", Json.mkObj worldSize)])
  return gameJson

def Game.merge (old : Game) (new : Game) : Game :=
{ new with
  worlds := {
    nodes := old.worlds.nodes.merge new.worlds.nodes World.merge
    edges := Id.run do
      let mut res := old.worlds.edges
      for e in new.worlds.edges do
        if ¬ res.contains e then
          res := res.insert e
      return res
  } }
