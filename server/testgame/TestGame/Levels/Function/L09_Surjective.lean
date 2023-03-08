import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Function"
Level 8

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
  intro y
  use y-1
  simp

NewDefinition Surjective

Hint : Surjective (fun (n : ℤ) ↦ n + 1) =>
"**Robo**: Die Definition von `Surjective f` ist `∀ y, (∃ x, f x = y)`.

**Du**: Dann kann ich das auch einfach wie Quantifier behandeln?

**Robo**: Schieß drauf los!"

Conclusion
"Der Gelehrte händigt euch schmunzelnd das Buch aus."
