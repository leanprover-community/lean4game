import TestGame.Metadata

import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Parity
import Mathlib.Tactic.Ring

import TestGame.ToBePorted

Game "TestGame"
World "SetTheory2"
Level 2

Title "Potenzmenge"

Introduction
"
Eine andere wichtige Menge ist die Potenzmenge einer Menge, welche als
`𝒫 A` geschrieben wird (`\\powerset`). Diese ist als `{S | S ⊆ A}` definiert, also
alle Mengen, die in $A$ enthalten sind.

Eines der wichtigsten Lemmas ist `mem_powerset_iff: x ∈ 𝒫 s ↔ x ⊆ s` welches
im Grunde die Definition einsetzt.
"

open Set

Statement
"" (X Y : Set ℕ):
    𝒫 X ∪ 𝒫 Y ⊆ 𝒫 (X ∪ Y)  := by
  intro A hA
  rw [mem_union] at hA
  simp_rw [mem_powerset_iff] at *
  rcases hA with hA | hA
  apply subset_union_of_subset_left
  assumption
  apply subset_union_of_subset_right
  assumption


NewTactics constructor intro rw assumption rcases simp tauto trivial

NewLemmas Subset.antisymm_iff empty_subset
