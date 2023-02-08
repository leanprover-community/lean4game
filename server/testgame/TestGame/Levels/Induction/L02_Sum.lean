import Mathlib.Algebra.BigOperators.Basic
import Mathlib

import TestGame.Metadata

set_option tactic.hygienic false

Game "TestGame"
World "Induction"
Level 2

Title "endliche Summe"

Introduction
"
Jetzt wollen wir ein paar Lemmas zu Summen kennenlernen, die `simp` nicht automatisch
verwendet.

Als erstes, kann man eine endliche Summe $\\sum_{i = 0}^n a_i + b_i$ mit
`rw [Finset.sum_add_distrib]` als zwei Summen $\\sum_{i = 0}^n a_i + \\sum_{j = 0}^n b_j$
auseinandernehmen.

Insbesondere ist auch zu beachten, dass der Index `i` keine natürliche Zahl ist, sondern
vom Typ `Fin n`, das heisst, man muss diesen eigentlich immer mit `(i : ℕ)`
als natürliche Zahl verwenden.
"

open BigOperators

Statement
"Zeige dass $\\sum_{i=0}^{n-1} (i + 1) = n + \\sum_{i=0}^{n-1} i$."
    (n : ℕ) : ∑ i : Fin n, ((i : ℕ) + 1) = n + (∑ i : Fin n, (i : ℕ)) := by
  rw [Finset.sum_add_distrib]
  simp
  ring

NewTactics rw simp ring
