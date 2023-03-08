import TestGame.Metadata

import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Parity
import Mathlib.Tactic.Ring

Game "TestGame"
World "SetTheory2"
Level 6

Title ""

Introduction
"
"

open Set

Statement
"" :
    3 ∈ {n : ℕ | Odd n}  := by
  rw [mem_setOf]
  use 1
  ring

NewTactic constructor intro rw assumption rcases simp tauto trivial

NewLemma Subset.antisymm_iff empty_subset
