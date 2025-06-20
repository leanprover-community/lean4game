import GameServer.Layer.Current
import GameServer.Layer.Defs
import GameServer.Layer.Extension
import GameServer.Layer.Game
import GameServer.Layer.Level
import GameServer.Layer.World

/-!
# Layers

A game consisists of multiple layers:

First, there is the `Game` itself. Each `Game` has mulitple `World`s and a `World`
contains multiple `Level`s.

The levels inside a world are ordered and indexed by natural numbers `1, 2, 3, …`. Level `0` is
reserved to display the world's "introduction text".

Worlds are indexed by there name. A game containes a directed graph which describes
the order of the worlds among each other.

# Important definitions

- `LevelId`: refers to a combination "game name, world name, level index"
-/
