import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Function"
Level 8

Title ""

Introduction
"
**Du**: Ehm, und wie kommen wir da wieder raus?

**Gelehrter**: Gerne zeige ich euch den Weg, nachdem ihr mir auch noch folgendes erklärt:
"

open Function

Statement "" : Bijective (fun (n : ℤ) ↦ n + 1) := by
  unfold Bijective
  constructor
  intro a b
  simp
  intro y
  use y-1
  simp

Hint : Bijective (fun (n : ℤ) ↦ n + 1) =>
"**Robo** *(flüsternd)*: `Bijectve f` ist als `Injective f ∧ Surjective f` definiert.

**Du**: Dann ist das ja ganz simpel!
"

Conclusion
"Zufrieden drückt euch der Gelehrte eine neue Fackel in die Hand und
zeigt euch den Weg nach draussen."

NewDefinition Bijective
