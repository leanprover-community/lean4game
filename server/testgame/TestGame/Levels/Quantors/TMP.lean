import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

Game "TestGame"
World "Contradiction"
Level 3

Title "Widerspruch"

Introduction
"
Ähnlich siehts aus, wenn man Annahmen hat, die direkte Negierung voneinander sind,
also `(h : A)` und `(g : ¬ A)`.
"

Statement
  "Ein Widerspruch impliziert alles."
    (A : Prop) (n : ℕ) (h : ∃ x, 2 * x = n) (g : ¬ (∃ x, 2 * x = n)) : A := by
  contradiction

Tactics contradiction
