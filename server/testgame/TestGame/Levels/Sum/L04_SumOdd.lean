import TestGame.Metadata

import TestGame.Options.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

Game "TestGame"
World "Sum"
Level 4

Title "Summe aller ungeraden Zahlen"

Introduction
"
Hier nochmals eine Übung zur Induktion.
"
set_option tactic.hygienic false

open BigOperators

Statement odd_arithmetic_sum
"Zeige folgende Gleichung zur Summe aller ungeraden Zahlen:

$\\sum_{i = 0}^n (2n + 1) = n ^ 2$."
    (n : ℕ) : (∑ i : Fin n, (2 * (i : ℕ) + 1)) = n ^ 2 := by
  induction' n with n hn
  simp
  rw [Fin.sum_univ_castSucc]
  simp
  rw [hn]
  rw [Nat.succ_eq_add_one]
  ring

HiddenHint (n : ℕ) : (∑ i : Fin n, (2 * (i : ℕ) + 1)) = n ^ 2 =>
"
Fange wieder mit `induction {n}` an.
"

HiddenHint : ∑ i : Fin Nat.zero, ((2 : ℕ) * i + 1) = Nat.zero ^ 2 =>
"
Den Induktionsanfang kannst du wieder mit `simp` beweisen.
"

HiddenHint (n : ℕ) : ∑ i : Fin (Nat.succ n), ((2 : ℕ) * i + 1) = Nat.succ n ^ 2 =>
"
Den Induktionsschritt startest du mit `rw [Fin.sum_univ_castSucc]`.
"

HiddenHint (n : ℕ) (hn : ∑ i : Fin n, (2 * (i : ℕ) + 1) = n ^ 2) :
  ∑ x : Fin n, (2 * (x : ℕ) + 1) + (2 * n + 1) = Nat.succ n ^ 2 =>
"
Hier kommt die Induktionshypothese {hn} ins Spiel.
"

HiddenHint (n : ℕ) : n ^ 2 + (2 * n + 1) = Nat.succ n ^ 2 =>
"
Mit `rw [Nat.succ_eq_add_one]` und `ring` kannst du hier abschliessen.
"
