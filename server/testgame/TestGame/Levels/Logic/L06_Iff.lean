import TestGame.Metadata

import Init.Data.ToString
#check List UInt8

Game "TestGame"
World "Logic"
Level 10

Title "Genau dann wenn"

Introduction
"
Genau-dann-wenn, $A \\iff B$, wird als `A ↔ B (`\\iff`) geschrieben.

Als erstes kann man mit `rw` Annahmen der Form `(h : A ↔ B)` genau gleich wie Gleichungen
`(h : a = b)` benützen, um das Goal umzuschreiben.

Hier also nochmals die Gleiche Aufgabe wie zuvor,
aber diesmal mit Iff-Statements von Aussagen anstatt
Gleichungen von natürlichen Zahlen.
"

Statement
    "Zeige dass `B ↔ C`."
    (A B C D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ C := by
  rw [h₁]
  rw [←h₂]
  assumption

Hint (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ C =>
"Im Goal kommt `C` vor und `h₁` sagt `C ↔ D`.
Probiers doch mit `rw [h₁]`."

Hint (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ D =>
"Zur Erinnerung: Man kann auch rückwärts umschreiben: `h₂` sagt `A ↔ b` mit
`rw [←h₂]` ersetzt man im Goal `b` durch `a` (`\\l`, also ein kleines L)"

Hint (A : Prop) (B : Prop) (h : A ↔ B) : A ↔ B =>
"Schau mal durch die Annahmen durch."



Tactics rw assumption
