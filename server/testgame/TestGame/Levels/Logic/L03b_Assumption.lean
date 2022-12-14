import TestGame.Metadata
import Mathlib.Data.Nat.Basic -- TODO

Game "TestGame"
World "Logic"
Level 4

Title "Logische Aussagen: `Prop`"

Introduction
"
Eine allgemeine logische Aussage definiert man mit `(A : Prop)`.

Damit sagt man noch nicht, ob die Aussage $A$ wahr oder falsch ist.
Mit einer Annahme `(hA : A)` nimmt man an, dass $A$ wahr ist:
`hA` ist sozusagen ein Beweis von $A$.
"

Statement mehr_triviales
    "Sei $A$ eine logische Aussage und sei `hA` ein Beweis für $A$.
    Zeige, dass $A$ wahr ist."
    (A : Prop) (hA : A) : A := by
  assumption

Hint (A : Prop) (hA : A) : A =>
"Auch hier kann `assumption` den Beweis von `A` finden."

Conclusion ""

Tactics assumption
