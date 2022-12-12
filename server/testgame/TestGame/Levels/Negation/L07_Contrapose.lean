import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import TestGame.ToBePorted

Game "TestGame"
World "Contradiction"
Level 7

Title "Kontraposition"

Introduction
"
Im Gegensatz dazu kann man auch einen Beweis durch Kontraposition führen.
Das ist kein Widerspruch, sondern benützt dass `A → B` und `(¬ B) → (¬ A)`
logisch equivalent sind.

Wenn das Goal eine Implikation ist, kann man `contrapose` anwenden.
"

Statement
    "Ist n² ungerade, so ist auch n ungerade. Beweise durch Kontraposition."
    (n : ℕ) : odd (n ^ 2) → odd n := by
  contrapose
  rw [not_odd]
  rw [not_odd]
  apply even_square

Tactics contrapose rw apply
Lemmas even odd not_even not_odd even_square
