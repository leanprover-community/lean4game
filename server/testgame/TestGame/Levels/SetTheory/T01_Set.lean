import TestGame.Metadata

import Mathlib.Order.SymmDiff
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Use
import Mathlib.Tactic.SolveByElim
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Lift
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.LibrarySearch
import Mathlib

set_option tactic.hygienic false

Game "TestGame"
World "SetTheory"
Level 1

Title "Mengen"

Introduction
"
In diesem Kapitel schauen wir uns Mengen an.

Zuerst ein ganz wichtiger Punkt: Alle Mengen in Lean sind homogen. Das heisst,
alle Elemente in einer Menge haben den gleichen Typ.

Zum Beispiel `{1, 4, 6}` ist eine Menge von natürlichen Zahlen. Aber man kann keine
Menge `{(2 : ℕ), {3, 1}, \"e\", (1 : ℂ)}` definieren, da die Elemente unterschiedliche Typen haben.

Für einen Typen `{X : Type*}` definiert damit also `set X` der Type aller Mengen mit Elementen aus
`X`.  `set.univ` ist dann ganz `X` also Menge betrachtet, und es ist wichtig den Unterschied
zu kennen: `(univ : set X)` und `(X : Typ*)` haben nicht den gleichen Typ und sind damit auch nicht
austauschbar!

Am anderen Ende sitzt die leere Menge `(∅ : set X)` (`\\empty`). Bei `univ` und `∅` versucht Lean
automatisch den Typ zu erraten, in exotischen Beispielen muss man wie oben diesen explizit angeben.

Als erste Operationen schauen wir uns `∪` (`\\union` oder `\\cup`), `∩`
(`\\inter` oder `\\cap`) und `\\` (`\\\\` oder `\\ `)

"

open Set

Statement
    "Wenn $B$ wahr ist, dann ist die Implikation $A \\Rightarrow (A ∧ B)$ wahr."
    {X : Type _} {A B : Set X} : univ \ (A ∩ B) ∪ ∅ = (univ \ A) ∪ (univ \ B) ∪ (A \ B) := by
  rw [Set.diff_inter]
  rw [Set.union_empty]
  rw [Set.union_assoc]
  rw [←Set.union_diff_distrib]
  rw [Set.univ_union]

Tactics rw


example : 4 ∈ (univ : Set ℕ) := by
  trivial

example (A : Set ℕ) : 4 ∉ (∅ : Set ℕ) := by
  trivial

example (A : Set ℕ) : A ⊆ univ := by
  intro x h
  trivial

-- -- subset_empty_iff
-- example {s : Set α} : s ⊆ ∅ ↔ s = ∅ := by
--   constructor
--   intro h
--   rw [Subset.antisymm_iff]
--   constructor
--   assumption
--   simp only [empty_subset]
--   intro a
--   rw [Subset.antisymm_iff] at a
--   rcases a with ⟨h₁, h₂⟩
--   assumption

-- -- eq_empty_iff_forall_not_mem
-- example {s : Set α} : s = ∅ ↔ ∀ x, x ∉ s := by
--   rw [←subset_empty_iff]
--   rfl

-- -- nonempty_iff_ne_empty
-- example (X : Type _) (s : Set X) : Set.Nonempty s ↔ s ≠ ∅ := by
--   rw [Set.Nonempty]
--   rw [ne_eq, eq_empty_iff_forall_not_mem]
--   push_neg
--   rfl


-- example (A B : ℝ): A = B ↔ A ≤ B ∧ B ≤ A := by library_search

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
  rw [mem_powerset_iff, subset_singleton_iff_eq]
  rw [mem_insert_iff, mem_singleton_iff]


lemma mem_powerset_insert_iff {U : Type _} (A S : Set U) (x : U) :
    S ∈ 𝒫 (insert x A) ↔ S \ {x} ∈ 𝒫 A := by
  rw [mem_powerset_iff, mem_powerset_iff, diff_singleton_subset_iff]

-- lemma powerset_insert {U : Type _} (A : Set U) (x : U) :
--     𝒫 (insert x A) = 𝒫 A ∪ ({B : Set U | B \ {x} ∈ 𝒫 A}) := by
--   sorry

theorem subset_insert_iff_of_not_mem {U : Type _ }{s t : Set U} (h : a ∉ s) : s ⊆ insert a t ↔ s ⊆ t := by
  rw [subset_insert_iff, erase_eq_of_not_mem h]

lemma mem_powerset_insert_iff₂ {U : Type _} (A S : Set U) (x : U) :
    S ∈ 𝒫 (insert x A) ↔ S ∈ 𝒫 A ∨ ∃ B ∈ 𝒫 A , insert x B = S := by
  simp_rw [mem_powerset_iff]
  constructor
  · intro h
    by_cases hs : x ∈ S
    · sorry
    · left
      rw [Finset.subset_insert_iff_of_not_mem]
  · intro h
    rcases h with h | ⟨B, h₁, h₂⟩
    · exact le_trans h (subset_insert x A)
    · rw [←h₂]
      exact insert_subset_insert h₁

lemma powerset_insert {U : Type _} (A : Set U) (x : U) :
    𝒫 (insert x A) = A.powerset ∪ A.powerset.image (insert x) := by
  rw [Subset.antisymm_iff]
  constructor <;>
  intro B hB <;>
  simp_rw [mem_powerset_insert_iff₂, mem_union, mem_image] at hB ⊢ <;>
  assumption


example : powerset {0, 1} = {∅, {0}, {1}, {0, 1}} := by
  simp_rw [powerset_insert, powerset_singleton, Finset.powerset_insert, Finset.powerset_singleton]
  simp only [image_insert_eq, union_insert, image_singleton, union_singleton]
  simp only [insert_comm, ←insert_emptyc_eq]

example [DecidableEq ℕ] : Finset.powerset {0, 1} = {∅, {0}, {1}, {0, 1}} := by
  repeat' rw [@ Finset.powerset_insert ℕ]
  repeat' rw [@Finset.powerset_singleton ℕ]
  --simp only [image_insert_eq, union_insert, image_singleton, union_singleton]


example : powerset {0, 1, 2, 4} =
    {∅, {0}, {1}, {0, 1}, {2}, {1, 2}, {0, 2}, {0, 1, 2},
    {4}, {0, 4}, {1, 4}, {0, 1, 4}, {2, 4}, {1, 2, 4}, {0, 2, 4}, {0, 1, 2, 4}} := by
  simp_rw [powerset_insert, powerset_singleton]
  simp_rw [image_insert_eq, image_singleton]



example : Finset.powerset ({0, 1} : Finset ℕ) = {{0, 1}, ∅, {1}, {0}} := by
  have h : Finset.powerset ({0, 1} : Finset ℕ) = {∅, {0}, {1}, {0, 1}}
  rfl
  rw [h]
  simp only []


example : ({∅, {0}, {1}, {0, 1}} : Finset (Finset ℕ)) = {∅, {1}, {0}, {0, 1}} := by
  simp only []



lemma subset_of_subset_diff {U : Type _} (A B C : Set U) (h : A ⊆ B \ C) : A ⊆ B :=
  fun _ hx => mem_of_mem_diff (h hx)

lemma subset_of_subset_diff' {U : Type _} (A B C : Set U) (h : A ⊆ B) : A \ C ⊆ B :=
  sorry

lemma mem_powerset' {U : Type _} {A B C : Set U}
    (h' : B ∈ 𝒫 C) (h : A ⊆ B) :
    A ∈ 𝒫 C := by
  rw [mem_powerset_iff] at h' ⊢
  exact le_trans h h'

example (A B : Set ℕ) : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B := by
  exact ext_iff



lemma NO.powerset_insert {U : Type _} (A : Set U) (x : U) :
    𝒫 (insert x A) = 𝒫 A ∪ ({insert x B | B ∈ 𝒫 A}) := by
  ext y
  rw [mem_powerset_insert_iff]
  constructor
  · intro h
    rw [mem_union, mem_setOf]
    by_cases hx : x ∈ y
    · right
      use y \ {x}
      constructor
      · assumption
      · rw [insert_diff_singleton, insert_eq_of_mem hx]
    · left
      rw [diff_singleton_eq_self hx] at h
      assumption
  · intro h
    rw [mem_union, mem_setOf] at h
    rcases h with h | h
    · apply mem_powerset' h
      simp
    · rcases h with ⟨B, hB⟩
      rw [←hB.2]
      apply mem_powerset' hB.1
      simp

-- lemma xxx {U : Type _} (x y : U):
--     ({insert x B | B ∈ {∅, }}) = {({x} : Set U), {x, y}} := by
--   sorry

-- lemma hh {U : Type _} (A : Set U) (x : U) :
--     A \ {x} ∈

lemma diff_singleton_eq_iff {U : Type _} {A B : Set U} {x : U} :
    A \ {x} = B ↔ A = B ∨ A = insert x B := by sorry

lemma x1 {U : Type _} (x : U) : insert x (∅ : Set U) = {x} := by sorry

--set_option maxHeartbeats 20000


example {U : Type _} {x y : U} : ({x, y} : Set U) = {y, x} := by
  exact pair_comm x y

example {U : Type _} {A : Set U} {x y : U} : insert x (insert y A) = insert y (insert x A) := by
  exact insert_comm x y A

open Classical

#check decide

example : ({{0, 2}, {3, 5, 6}} : Set (Set ℕ)) = {{2, 0}, {5, 3, 6}} := by
  rw [Subset.antisymm_iff]
  constructor <;>
  intro A hA <;>
  simp_rw [mem_insert_iff, mem_singleton_iff] at *
  · rw [pair_comm 2 0, insert_comm 5 3]
    tauto
  · rw [pair_comm 0 2, insert_comm 3 5]
    tauto

example (A : Set ℕ) : ({{0, 2}, A, {3, 5, 6}} : Set (Set ℕ)) = {{2, 0}, {5, 3, 6}, A} := by
  simp only [insert_comm, ←insert_emptyc_eq]


example : ({{0, 2}, {3, 5, 6}} : Finset (Finset ℕ)) = {{2, 0}, {5, 3, 6}} := by
  simp only


  -- -- This works but does not scale well
  -- ext x
  -- simp_rw [powerset_insert, powerset_singleton]
  -- simp_rw [mem_union, mem_setOf, mem_insert_iff, mem_singleton_iff]
  -- simp_rw [diff_singleton_eq_iff, x1]
  -- tauto




  -- rw [Subset.antisymm_iff]
  -- constructor
  -- intro A hA
  -- rw [mem_powerset_iff] at hA
  -- simp_rw [mem_insert_iff, mem_singleton_iff] at *


example : ({2, 3, 5} : Set ℕ) ⊆ {4, 2, 5, 7, 3} := by
  intro a ha
  simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at *
  tauto

example : ({0} : Set ℕ) ∪ {1, 2} = {0, 2, 1} := by
  rw [Subset.antisymm_iff]
  intro A hA
  --rw [Set.mem_insert_iff]



-- Trick:
-- attribute [default_instance] Set.instSingletonSet
