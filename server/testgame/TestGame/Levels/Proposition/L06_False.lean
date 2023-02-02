import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

Game "TestGame"
World "Proposition"
Level 7

Title "Widerspruch beweist alles."

Introduction
"
Die Aussage `False` ist für uns wichtiger als `True`, da ein Beweis der falschen Aussage
`False` einen Widerspruch repräsentiert.
Hat man einen Widerspruch, kann man daraus mit der Taktik `contradiction` alles beweisen.

Der erste Widerspruch, den `contradiction` erkennt, ist ein Beweis von `False`.
"

Statement
"Sei $A$ eine Aussage und angenommen man hat einen Beweis für `False`.
Zeige, dass daraus $A$ folgt."
    (A : Prop) (h : False) : A := by
  contradiction

HiddenHint (A : Prop) (h : False) : A =>
"Wenn man einen Beweis von `False` hat, kann man mit `contradiction` das Goal beweisen,
unabhängig davon, was das Goal ist."

Tactics contradiction
