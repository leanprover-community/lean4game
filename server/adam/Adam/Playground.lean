-- import Mathlib.Data.Set.Basic
-- import Mathlib

-- open Function Set

-- example {A B : Type _ } (f : A → B) : f.Injective ↔ ∃ g : B → A, g ∘ f = id := by
--   constructor
--   · intro h
--     -- hard.
--     sorry
--   · intro h
--     rcases h with ⟨g, h⟩
--     unfold Injective
--     intro a b hab
--     rw [←id_eq a, ←id_eq b]
--     rw [← h]
--     rw [comp_apply]
--     rw [hab]
--     simp


-- lemma singleton_mem_powerset
--     {U : Type _} {M : Set U} {x : U} (h : x ∈ M) :
--     {x} ∈ 𝒫 M := by
--   rw [mem_powerset_iff, singleton_subset_iff]
--   assumption

-- example
--     {U : Type _} (M : Set U) :
--     {A : Set U // A ∈ 𝒫 M} = {A ∈ 𝒫 M | True} := by
--   simp_rw [coe_setOf, and_true]

-- example
--     {U : Type _} (M : Set U) :
--     {A : Set U // A ∈ 𝒫 M} = 𝒫 M := by
--   rfl

-- example
--     {U : Type _} (M : Set U) :
--     {x : U // x ∈ M} = M := by
--   rfl

-- example
--     {U : Type _} (M : Set U) :
--     ∃ (f : M → 𝒫 M), Injective f := by
--   use fun x ↦ ⟨ _, singleton_mem_powerset x.prop ⟩
--   intro a b hab
--   simp at hab
--   rw [Subtype.val_inj] at hab
--   assumption

-- instance {U : Type _} {M : Set U} : Membership ↑M ↑(𝒫 M) :=
-- { mem := fun x A ↦ x.1 ∈ A.1 }

-- instance {U : Type _} {M : Set U} : Membership U (Set ↑M) :=
-- { mem := fun x A ↦ _ }


-- example
--     {U : Type _} {M : Set U} (h_empty : M.Nonempty)
--     (f : {x : U // x ∈ M} → {A : Set U // A ∈ 𝒫 M}):
--     ¬ Surjective f := by
--   unfold Surjective
--   push_neg
--   --by_contra h_sur
--   let B : Set M := {x : M | x ∉ (f x)}
--   use ⟨B, sorry⟩
--   intro ⟨a, ha⟩
--   sorry
--   -- Too hard?

-- #check singleton_mem_powerset
-- #check Subtype.val_inj



-- -- These are fun exercises for prime.
-- example (x : ℕ) : 0 < x ↔ 1 ≤ x := by
--   rfl

-- lemma le_cancel_left (n x : ℕ) (h : x ≠ 0): n ≤ n * x := by
--   induction n
--   simp
--   simp
--   rw [← zero_lt_iff] at h
--   assumption


-- example (n m : ℕ) (g : m ≠ 0) (h : n ∣ m) : n ≤ m := by
--   rcases h with ⟨x, hx⟩
--   rw [hx]
--   apply le_cancel_left
--   by_contra k
--   rw [k] at hx
--   simp at hx
--   rw [hx] at g
--   contradiction
