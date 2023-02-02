import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

import TestGame.ToBePorted

Game "TestGame"
World "Proposition"
Level 8

Title "Widerspruch"

Introduction
"
Zweitens kann `contradiction` auch aus Annahmen der Form `a ≠ a` einen Widerspruch finden.

*Bemerkung:* Das Ungleichzeichen `≠` (`\\ne`) sollte immer als `¬(· = ·)` gelesen werden.
"

Statement
"Sei $n$ eine natürliche Zahl die ungleich sich selbst ist. Dann ist $n = 37$."
    (n : ℕ) (h : n ≠ n) : n = 37 := by
  contradiction

Conclusion
"
"

Tactics contradiction
