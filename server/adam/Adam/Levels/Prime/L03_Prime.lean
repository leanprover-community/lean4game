import Adam.Metadata
import Adam.Options.MathlibPart

import Adam.ToBePorted

Game "Adam"
World "Prime"
Level 3

Title "Primzahlen"

Introduction
"
Der Lehrer erklärt sein Problem.

**Lehrer**: Und dann fragte der Schüler, wie man denn folgendes herleitet.
Und dabei ist das weit über seiner Altersstufe!
"

Statement
  (p : ℕ) (h₂ : 2 ≤ p): Nat.Prime p ↔ ∀ (a b : ℕ), p ∣ a * b → p ∣ a ∨ p ∣ b := by
  Hint "**Du**: Naja, mal schauen wie weit man mit `intro` und `constructor` kommt…"
  constructor
  intro h a b
  Hint "**Robo**: Stop! Hier helfe ich dir etwas"
  apply (Nat.Prime.dvd_mul h).mp
  intro h
  rw [Nat.prime_iff]
  unfold Prime
  rw [Nat.isUnit_iff, ←and_assoc]
  constructor
  constructor
  linarith
  linarith
  assumption
