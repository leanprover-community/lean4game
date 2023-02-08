import TestGame.Metadata
import Mathlib.Tactic.Ring
import Mathlib


Game "TestGame"
World "Induction"
Level 3

Title "Induktion"

Introduction
"
Induktion ist eine wichtige Beweismethode, nicht zuletzt auch wenn es um endliche Summen geht.

Die Taktik `induction' n with n n_ih` teilt das Goal in zwei Goals auf:

1. Induktionsanfang, wo `n` durch `0` ersetzt wird.
2. Induktionsschritt, wo `n` durch `n.succ` (also `(n + 1)`) ersetzt wird und man die
   Induktionshypothese als Annahme `n_ih` kriegt.

Für den Induktionsschritt braucht man fast immer zwei technische Lemmas:

- `Fin.sum_univ_castSucc` um $\\sum_{i=0}^{n} a_i$ als
  $\\sum_{i=0}^{n-1} a_i + a_n$ umzuschreiben.
- `nat_succ` um `n.succ` zu `n + 1` umzuschreiben.
"

-- Note: I don't want to deal with Nat-division, so I stated it as `2 * ... = ...` instead.

open BigOperators

Statement arithmetic_sum
"Zeige $\\sum_{i = 0}^n i = \\frac{n \\cdot (n + 1)}{2}$."
  (n : ℕ) : 2 * (∑ i : Fin (n + 1), ↑i) = n * (n + 1) := by
  induction' n with n hn
  simp
  rw [Fin.sum_univ_castSucc]
  rw [mul_add]
  simp
  rw [mul_add, hn]
  simp_rw [Nat.succ_eq_one_add]
  ring

Tactics ring
