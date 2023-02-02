import TestGame.Metadata

import Mathlib.Data.Set.Basic

Game "TestGame"
World "SetTheory"
Level 9

Title "Komplement"

Introduction
"
Das Komplement einer Menge wird als `Aᶜ` (`\\^c`) geschrieben. Wichtige Lemmas
sind `not_mem_compl_iff` und `compl_eq_univ_diff`.
"

open Set

#check not_mem_compl_iff
#check compl_eq_univ_diff

Statement
""
    (A : Set ℕ) (h : Aᶜ ⊆ A) : A = univ := by
  apply Subset.antisymm
  simp only [subset_univ]
  intros x hx
  by_cases h4 : x ∈ Aᶜ
  exact mem_of_subset_of_mem h h4
  rw [←not_mem_compl_iff]
  exact h4

Tactics constructor intro rw assumption rcases simp tauto trivial

Lemmas Subset.antisymm_iff empty_subset
