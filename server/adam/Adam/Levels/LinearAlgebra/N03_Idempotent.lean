import Adam.Metadata

import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basic

Game "Adam"
World "Module2"
Level 3

Title "Lineare Abbildung"

Introduction
"

"

Statement
""
    {R V : Type _} [Semiring R] [AddCommGroup V] [Module R V]
    (p : V →ₗ[R] V) (h : p ∘ p = p) : LinearMap.ker p ⊔ LinearMap.range p = ⊤ := by
  sorry
  --   rw eq_top_iff,
  -- intros v hv,

  -- rw ←sub_add_cancel v (p v),

  -- apply submodule.add_mem_sup,
  -- { rw [linear_map.mem_ker],
  --   rw [map_sub],
  --   change p v - (p ∘ p) v = 0,  -- oder: rw [function.comp, function.funext_iff] at h,
  --   rw h,
  --   simp },
  -- { simp }
