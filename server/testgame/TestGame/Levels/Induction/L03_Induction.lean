import TestGame.Metadata
import Mathlib.Tactic.Ring
import Mathlib

import TestGame.ToBePorted

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

Statement
"Zeige $\\sum_{i = 0}^n i = \\frac{n ⬝ (n + 1)}{2}$."
  (n : ℕ) : 2 * (∑ i : Fin (n + 1), ↑i) = n * (n + 1) := by
  induction n
  simp

  sorry
  -- rw [Fin.sum_univ_castSucc]
  -- simp [nat_succ]
  -- rw [mul_add, hn]
  -- ring

Tactics ring