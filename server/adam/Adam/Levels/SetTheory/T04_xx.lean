-- import Adam.Metadata


-- import Duper.Tactic


-- import Mathlib.Order.Disjoint

-- set_option tactic.hygienic false

-- Game "Adam"
-- World "SetTheory"
-- Level 4

-- Title "Mengen"

-- Introduction
-- "
-- `∈ ∉ ⊆ ⊂ ⋃ ⋂`
-- "

-- open Set

-- -- open_locale cardinal

-- variables {X : Type _} (x : X) (A B : Set X)

-- #check A.Nonempty
-- #check Nonempty A
-- #check insert x A -- {x} ∪ A
-- -- #check disjoint A B -- needs Mathlib.Order.Disjoint
-- #check A ∆ B
-- #check Nontrivial A

-- #check ({2} : Set ℕ)

-- example : ({2} : Set ℕ) ⊆ {4, 2, 3} := by
--   simp only [mem_singleton_iff, mem_insert_iff, or_self, singleton_subset_iff, or_false, or_true]

-- example : ({2, 3, 5} : Set ℕ) ⊆ {4, 2, 5, 7, 3} := by
--   intro n hn
--   simp only [mem_insert_iff, mem_singleton_iff] at *
--   tauto

-- example : {2, 3, 5} ⊆ (univ : Set ℕ) := by
--   tauto

-- example : 3 ∈ ({4, 2, 5, 7, 3} : Set ℕ) := by
--   tauto

-- example : ({4, 9} : Set ℕ) = Set.insert 4 {9} := by
--   rfl




-- #check Finset.card

-- variable (A : Finset ℕ)

-- #check A.card

-- -- card_union_eq
-- example (A B : Finset ℕ) (h : Disjoint A B) : (A ∪ B).card = A.card + B.card := by
--   -- Not a suitable proof for the course.
--   rw [← Finset.disjUnion_eq_union A B h, Finset.card_disjUnion _ _ _]

-- example : ¬Disjoint {n : ℤ | ∃ k, n = 2 * k} {3, 5, 6, 9, 11} := by
--   rw [not_disjoint_iff]
--   use 6
--   constructor
--   rw [mem_setOf_eq]
--   use 3
--   tauto

-- example : {n : ℕ | Even n ∨ Odd n} = univ := by
--   rw [setOf_or]




-- #check Set.eq_of_mem_singleton
-- #check {n : ℤ | ∃ k, n = 2 * k}
-- #check {n : ℤ // ∃ k, n = 2 * k}
-- #check ℤ
-- variables (C : Set ℤ)
-- #check {n ∈ C | ∃ (k : ℤ), n = 2 * k}
-- #check {n : ℤ | n ∈ C ∧ ∃ (k : ℤ), n = 2 * k}
-- #check {x ∈ A | x = x}
-- #check {y | y ∈ A}
-- #check setOf_and
-- #check setOf_or
-- #check Disjoint C univ

-- example : {n ∈ C | ∃ (k : ℤ), n = 2 * k} = {n : ℤ | n ∈ C ∧ ∃ (k : ℤ), n = 2 * k} := by
--   rfl
