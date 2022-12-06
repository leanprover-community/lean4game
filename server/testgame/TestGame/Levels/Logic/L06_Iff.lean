import TestGame.Metadata

import Init.Data.ToString
#check List UInt8

Game "TestGame"
World "TestWorld"
Level 9

Title "Genau dann wenn"

Introduction
"
Genau-dann-wenn `A ↔ B` (`\\iff`) besteht aus zwei Implikationen `A → B` und `B → A`.

Als erstes kann man mit `rw` Annahmen der Form `(h : A ↔ B)` genau gleich wie Gleichungen
`(h : a = b)` benützen, um das Goal umzuschreiben.

Hier also nochmals die Gleiche Aufgabe, aber diesmal mit Iff-Statements von Aussagen anstatt
Gleichungen von natürlichen Zahlen.
"

Statement
    "
    Zeige dass `B ↔ C`.
    "
    (A B C D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ C := by
  rw [h₁]
  rw [←h₂]
  assumption

Tactics rw assumption
