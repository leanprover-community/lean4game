import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

Game "TestGame"
World "Contradiction"
Level 1

Title "Widerspruch beweist alles."

Introduction
"
Ein wichtiges Konzept ist die Verneinung und damit einhergehend die Kontraposition
und der Widerspruch (Kontradiktion).

Als allererstes der Widerspruch.

Wenn man in den Annahmen einen Widerspruch hat, kann man mit `contradiction` den Beweis
schliessen, denn ein Widerspruch beweist alles.

Der einfachste Widerspruch ist wenn man einen Beweis von `false` hat:
"

Statement
  "Ein Widerspruch impliziert alles."
    (A : Prop) (h : false) : A := by
  contradiction

Tactics contradiction
