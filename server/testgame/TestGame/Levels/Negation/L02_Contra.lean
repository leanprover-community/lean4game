import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

import TestGame.ToBePorted

Game "TestGame"
World "Contradiction"
Level 2

Title "Ad absurdum"

Introduction
"
Ähnlich siehts aus, wenn man Annahmen hat, die direkte Negierung voneinander sind,
also `(h : A)` und `(g : ¬ A)`. (`\\not`)
"

Statement
    "Ein Widerspruch impliziert alles."
    (n : ℕ) (h : even n) (g : ¬ (even n)) : n = 128 := by
  contradiction

Conclusion
"
"

Tactics contradiction
