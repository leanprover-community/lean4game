import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

import TestGame.ToBePorted

Game "TestGame"
World "Proposition"
Level 8

Title "Aus Falschem folgt vieles."

Introduction
"
Auftritt zweiter Querulant.
"

Statement ""
  (n : ℕ) (h : n ≠ n) : n = 37 := by
  contradiction

Hint (n : ℕ) (h : n ≠ n) : n = 37 =>
"
**Du** Ist `{n} ≠ {n}` nicht auch ein Widerspruch?

**Robo** Probiers mal!
"

Conclusion
"
**Du** Ja, scheint funktioniert zu haben.

**Du** Aber irgendwie kommt mir das immer noch ein wenig suspekt vor.
Jetzt habe ich bewiesen, dass eine beliebige natürliche Zahl gleich 37 ist?

**Robo** Nein, nicht doch.  Nur eine beliebige Zahl, die ungleich sich selbst ist, ist gleich 37.
Und gleich 38, und gleich 39, …

**Du** Ok, ok, verstehe.
"

NewTactics contradiction
DisabledTactics tauto
