import TestGame.Metadata

import TestGame.Options.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

import TestGame.Options.ArithSum

set_option tactic.hygienic false

open BigOperators

Game "TestGame"
World "Sum"
Level 5

Title "Summe vertauschen"

Introduction
"
Verschachtelte endliche Summen kann man beliebig tauschen.

$$\\sum_{i=0}^n\\sum_{j=0}^m a_{ij} = \\sum_{j=0}^m\\sum_{i=0}^n a_{ij}$$

Dieses Lemma heisst `Finset.sum_comm`
"


Statement
"Zeige dass
$\\sum_{i=0}^n\\sum_{j=0}^m  2^i (1 + j) = \\sum_{j=0}^m\\sum_{i=0}^n  2^i (1 + j)$."
    (n m : ℕ) : ∑ i : Fin n, ∑ j : Fin m, ( 2^i * (1 + j) : ℕ) =
    ∑ j : Fin m, ∑ i : Fin n, ( 2^i * (1 + j) : ℕ) := by
  rw [Finset.sum_comm]

NewLemmas Finset.sum_comm
