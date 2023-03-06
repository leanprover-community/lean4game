import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

import TestGame.ToBePorted

Game "TestGame"
World "Proposition"
Level 9

Title "Widerspruch"

Introduction
"
Auftritt dritter Querulant.
"

Statement ""
  (n : ℕ) (h : n = 10) (g : (n ≠ 10)) : n = 42 := by
  contradiction

Hint (n : ℕ) (h : n = 10) (g : (n ≠ 10)) : n = 42 =>
"
**Du** Wieder ein Widerspruch in den Annahmen?
"

Conclusion
"
**Robo** Gut gemacht.  Bei dieser Frage ist auch ein bisschen offensichtlicher, worin der Widerspruch besteht:  Die Annahme `n ≠ 10` ist genau die Negation von `n = 10`.   Man muss `≠` immer als `¬(· = ·)` lesen.
"

NewTactics contradiction
DisabledTactics tauto
