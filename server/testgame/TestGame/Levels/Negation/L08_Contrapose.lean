import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import TestGame.ToBePorted

Game "TestGame"
World "Contradiction"
Level 8

Title "Kontraposition"

Introduction
"
Lean Trick: Wenn das Goal nicht bereits eine Implikation ist, sondern man eine Annahme `h` hat, die
Man gerne für die Kontraposition benützen würde, kann man mit `revert h` diese als
Implikationsannahme ins Goal schreiben.
"

Statement
    "Ist n² ungerade, so ist auch n ungerade. Beweise durch Kontraposition."
    (n : ℕ) (h : odd (n ^ 2)): odd n := by
  revert h
  contrapose
  rw [not_odd]
  rw [not_odd]
  apply even_square

Tactics contrapose rw apply revert
Lemmas even odd not_even not_odd even_square
