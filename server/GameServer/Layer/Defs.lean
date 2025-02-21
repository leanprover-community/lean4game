
namespace GameServer

open Lean

/--
A game has three layers: Game, World, Levels. These are set with the commands
`Game`, `World`, and `Level`. Commands like `Introduction` depend on the current level.
-/
inductive Layer where
  | Game
  | World
  | Level

/-- The default game name if `Game "MyGame"` is not used. -/
def defaultGameName: String := "MyGame"
-- Note: When changing any of these default names, one also needs to change them in `index.mjs`
