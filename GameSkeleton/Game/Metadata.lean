import GameApi
import Game.Doc

-- import Mathlib.Tactic.Common

/-!
Use this file to add things that should be available in all levels.

For example, here would be a good place to import mathlib tactics.

*Note*: As long as `Game.lean` exists and ends with the `MakeGame` command,
you are completely free how you structure your lean project, this is merely
a suggestion.

*Bug*: However, things are bugged out if the levels of different worlds are imported
in a random order. Therefore, you should keep the structure of one file Lean file per world
which imports all its levels. In different world, you *must not* import a single level of a different
world; only import entire worlds!
-/
