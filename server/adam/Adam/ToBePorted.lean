import Mathlib

open BigOperators

/-! # Delab Problems -/

open Lean PrettyPrinter Delaborator SubExpr

@[delab app.Finset.sum]
def delabFinsetSum : Delab := do
  guard $ (← getExpr).getAppNumArgs == 5
  guard $ ((← getExpr).getArg! 3).isAppOf' ``Finset.univ
  guard $ ((← getExpr).getArg! 4).isLambda
  withNaryArg 4 do
    let α ← withBindingDomain delab
    withBindingBodyUnusedName fun n => do
      let n : TSyntax `ident := ⟨n⟩
      let b ← delab
      `(∑ $n:ident : $α, $b)




/-! # Other Stuff -/

-- lemma not_odd {n : ℕ} : ¬ Odd n ↔ Even n := by
--   sorry

-- lemma not_even {n : ℕ} : ¬ Even n ↔ Odd n := by
--   sorry

lemma even_square (n : ℕ) : Even n → Even (n ^ 2) := by
  intro ⟨x, hx⟩
  unfold Even at *
  use 2 * x ^ 2
  rw [hx]
  ring

-- section powerset

-- open Set

-- namespace Finset

-- theorem powerset_singleton {U : Type _} [DecidableEq U] (x : U) :
--     Finset.powerset {x} = {∅, {x}} := by
--   ext y
--   rw [mem_powerset, subset_singleton_iff, mem_insert, mem_singleton]

-- end Finset

-- /- The powerset of a singleton contains only `∅` and the singleton. -/
-- theorem powerset_singleton {U : Type _} (x : U) :
--     𝒫 ({x} : Set U) = {∅, {x}} := by
--   ext y
--   rw [mem_powerset_iff, subset_singleton_iff_eq, mem_insert_iff, mem_singleton_iff]

-- theorem subset_insert_iff_of_not_mem' {U : Type _ } {s t : Set U} {a : U} (h : a ∉ s)
--     (g : s ⊆ t) : s ⊆ insert a t := by
--   intro y hy
--   specialize g hy
--   exact mem_insert_of_mem _ g

-- lemma mem_powerset_insert_iff {U : Type _} (A S : Set U) (x : U) :
--     S ∈ 𝒫 (insert x A) ↔ S ∈ 𝒫 A ∨ ∃ B ∈ 𝒫 A , insert x B = S := by
--   simp_rw [mem_powerset_iff]
--   constructor
--   · intro h
--     by_cases hs : x ∈ S
--     · right
--       use S \ {x}
--       rw [insert_diff_singleton, insert_eq_of_mem hs, diff_singleton_subset_iff]
--       exact ⟨h, rfl⟩
--     · left
--       exact (subset_insert_iff_of_not_mem hs).mp h
--   · intro h
--     rcases h with h | ⟨B, h₁, h₂⟩
--     · exact le_trans h (subset_insert x A)
--     · rw [←h₂]
--       exact insert_subset_insert h₁

-- lemma mem_powerset_insert_iff' {U : Type _} (A S : Set U) (x : U) :
--     S ∈ 𝒫 (insert x A) ↔ S \ {x} ∈ 𝒫 A := by
--   rw [mem_powerset_iff, mem_powerset_iff, diff_singleton_subset_iff]

-- lemma powerset_insert {U : Type _} (A : Set U) (x : U) :
--     𝒫 (insert x A) = A.powerset ∪ A.powerset.image (insert x) := by
--   ext y
--   rw [mem_powerset_insert_iff, mem_union, mem_image]



-- end powerset
