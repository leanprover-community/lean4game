import TestGame.Metadata

import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Span

Game "TestGame"
World "Module2"
Level 9

Title "Lineare Abbildung"

Introduction
"

"

universe u

variable {K : Type u} [Field K]
variable {ι : Type u} {V : ι → Type u}
variable [∀i, AddCommMonoid (V i)] [∀i, Module K (V i)]

/-
Ein externes Summe von Vektorräumen schreibt man mit `\Pi\0`, also `Π₀ i, V i`.
Das Suffix `_₀` wird in Mathlib häufig dafür verwendet "endlichen Support" zu bezeichnen.

-/
example : Module K (Π₀ i, V i) := inferInstance

variable {U : Type u} [AddCommMonoid U] [Module K U]

Statement
"" : True := by
  sorry

-- -- :(
-- variable [decidable_eq ι]
-- variable [Π (i : ι) (x : V i), decidable (x ≠ 0)]

-- def my_sum_map (f : Π i, V i →ₗ[K] U) : (Π₀ i, V i) →ₗ[K] U :=
-- { to_fun := λ x, x.sum (λ i, (f i)),
--   map_add' :=
--   begin
--     intros,
--     funext,
--     sorry,
--   end,
--   map_smul' :=
--   begin
--     intros,
--     funext,
--     simp,
--     sorry
--   end }

-- Statement
-- "Sei `U` ein `K`-Vektorraum und `fᵢ : Vᵢ → U` eine Familie von `K`-lineare Abbildungen
-- in `K`-Vektorräume. Dann gibt es genau eine Abbildung `f : (Π₀ i, V i) → U`, die mit
-- allen kommutiert."
--      (f : ∀ i, V i →ₗ[K] U) :
--   ∃! (g : (Π₀ i, V i) →ₗ[K] U), (∀ i v, f i v = g (dfinsupp.single i v)) :=
-- by
--   let g := my_sum_map f,
--   use g,
--   constructor,
--   { simp,
--     intros,
--     sorry },
--   { intros g' h,
--     apply linear_map.ext,
--     intro x,
--     sorry
--     -- change (λ i, g' x i) = λ i, f i x, -- Wieso?
--     -- funext,
--     -- symmetry,
--     -- apply h,
--   }
