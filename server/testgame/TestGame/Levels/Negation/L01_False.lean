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

Der einfachste Widerspruch ist wenn man einen Beweis von `False` hat:
"

Statement
    "Sei $A$ eine Aussage und angenommen man hat einen Beweis für `False`.
    Zeige, dass daraus $A$ folgt."
    (A : Prop) (h : False) : A := by
  contradiction

Message (A : Prop) (h : False) : A =>
"Wenn man einen Beweis von `False` hat, kann man mit `contradiction` das Goal beweisen,
unabhängig davon, was das Goal ist."

Tactics contradiction
