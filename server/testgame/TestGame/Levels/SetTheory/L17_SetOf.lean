import TestGame.Metadata

import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Parity
import Mathlib

Game "TestGame"
World "SetTheory2"
Level 4

Title ""

Introduction
"
"

open Set

Statement
"" :
    {2, 7} ⊆ {n : ℕ | n = 2 ∨ (n ≤ 10 ∧ Odd n)}  := by
  rw [setOf_or, setOf_and]
  intro x hx
  rw [mem_union, mem_inter_iff]
  simp_rw [mem_setOf, mem_insert_iff, mem_singleton_iff] at *
  rcases hx with hx | hx
  left
  assumption
  right
  constructor
  linarith
  use 3
  rw [hx]
  ring


NewTactics constructor intro rw assumption rcases simp tauto trivial

NewLemmas Subset.antisymm_iff empty_subset
