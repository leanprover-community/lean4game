

open Set

namespace Finset

theorem powerset_singleton {U : Type _} [DecidableEq U] (x : U) :
    Finset.powerset {x} = {∅, {x}} := by
  ext y
  rw [mem_powerset, subset_singleton_iff, mem_insert, mem_singleton]

end Finset

/- The powerset of a singleton contains only `∅` and the singleton. -/
theorem powerset_singleton {U : Type _} (x : U) :
    𝒫 ({x} : Set U) = {∅, {x}} := by
  ext y
  rw [mem_powerset_iff, subset_singleton_iff_eq, mem_insert_iff, mem_singleton_iff]

theorem subset_insert_iff_of_not_mem {U : Type _ } {s t : Set U} {a : U} (h : a ∉ s)
    : s ⊆ insert a t ↔ s ⊆ t := by
  constructor
  · intro g y hy
    specialize g hy
    rw [mem_insert_iff] at g
    rcases g with g | g
    · rw [g] at hy
      contradiction
    · assumption
  · intro g y hy
    specialize g hy
    exact mem_insert_of_mem _ g

theorem subset_insert_iff_of_not_mem' {U : Type _ } {s t : Set U} {a : U} (h : a ∉ s)
    (g : s ⊆ t) : s ⊆ insert a t := by
  intro y hy
  specialize g hy
  exact mem_insert_of_mem _ g

lemma mem_powerset_insert_iff {U : Type _} (A S : Set U) (x : U) :
    S ∈ 𝒫 (insert x A) ↔ S ∈ 𝒫 A ∨ ∃ B ∈ 𝒫 A , insert x B = S := by
  simp_rw [mem_powerset_iff]
  constructor
  · intro h
    by_cases hs : x ∈ S
    · right
      use S \ {x}
      rw [insert_diff_singleton, insert_eq_of_mem hs, diff_singleton_subset_iff]
      exact ⟨h, rfl⟩
    · left
      exact (subset_insert_iff_of_not_mem hs).mp h
  · intro h
    rcases h with h | ⟨B, h₁, h₂⟩
    · exact le_trans h (subset_insert x A)
    · rw [←h₂]
      exact insert_subset_insert h₁

lemma mem_powerset_insert_iff' {U : Type _} (A S : Set U) (x : U) :
    S ∈ 𝒫 (insert x A) ↔ S \ {x} ∈ 𝒫 A := by
  simp_rw [mem_powerset_iff, diff_singleton_subset_iff]

lemma powerset_insert {U : Type _} (A : Set U) (x : U) :
    𝒫 (insert x A) = A.powerset ∪ A.powerset.image (insert x) := by
  ext y
  rw [mem_powerset_insert_iff, mem_union, mem_image]





example : ({0} : Set ℕ) ∪ {1, 2} = {0, 2, 1} := by
  rw [union_insert, singleton_union]
  simp only [insert_comm, ←insert_emptyc_eq]

example : powerset {0, 1} = {∅, {0}, {1}, {0, 1}} := by
  simp_rw [powerset_insert, powerset_singleton]
  simp only [image_insert_eq, union_insert, image_singleton, union_singleton]
  simp only [insert_comm, ←insert_emptyc_eq]

-- This one is much slower, but it still works
example : powerset {0, 1, 2, 4} =
    {∅, {0}, {1}, {0, 1}, {2}, {1, 2}, {0, 2}, {0, 1, 2},
    {4}, {0, 4}, {1, 4}, {0, 1, 4}, {2, 4}, {1, 2, 4}, {0, 2, 4}, {0, 1, 2, 4}} := by
  simp_rw [powerset_insert, powerset_singleton]
  simp only [image_insert_eq, union_insert, image_singleton, union_singleton]
  simp only [insert_comm, ←insert_emptyc_eq]

example : ({∅, {0}, {1}, {0, 1}} : Finset (Finset ℕ)) = {∅, {1}, {0}, {0, 1}} := by
  simp only []

example : ({{0, 2}, {3, 5, 6}} : Set (Set ℕ)) = {{2, 0}, {5, 3, 6}} := by
  rw [Subset.antisymm_iff]
  constructor <;>
  intro A hA <;>
  simp_rw [mem_insert_iff, mem_singleton_iff] at *
  · rw [pair_comm 2 0, insert_comm 5 3]
    tauto
  · rw [pair_comm 0 2, insert_comm 3 5]
    tauto

-- A trick to compare two concrete sets.
example (A : Set ℕ) : ({{0, 2}, A, {3, 5, 6}} : Set (Set ℕ)) = {{2, 0}, {5, 3, 6}, A} := by
  simp only [insert_comm, ←insert_emptyc_eq]

example : ({{0, 2}, {3, 5, 6}} : Finset (Finset ℕ)) = {{2, 0}, {5, 3, 6}} := by
  simp only

-- Trick:
-- attribute [default_instance] Set.instSingletonSet
