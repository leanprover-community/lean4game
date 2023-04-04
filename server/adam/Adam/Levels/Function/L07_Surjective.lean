import Adam.Metadata

import Adam.Options.MathlibPart

Game "Adam"
World "Function"
Level 7

Title "Surjektive"

Introduction
"
Endlich kommt ihr in einen große, beleuchteten zentralen Raum.
Alle Wände sind voll mit Büchern und
in der Mitte sitzt an einem einsamen
Tisch ein Gelehrter, der tatsächlich das gesuchte Buch zeigen kann.

Bevor er dieses aushändigt, will er aber folgendes wissen:
"

open Function

Statement "" : Surjective (fun (n : ℤ) ↦ n + 1) := by
  Hint "**Robo**: Die Definition von `Surjective f` ist `∀ y, (∃ x, f x = y)`.

  **Du**: Dann kann ich das auch einfach wie Quantifier behandeln?

  **Robo**: Schieß drauf los!"
  intro y
  use y-1
  simp

NewDefinition Surjective
LemmaTab "Function"

Conclusion
"Der Gelehrte händigt euch schmunzelnd das Buch aus."
