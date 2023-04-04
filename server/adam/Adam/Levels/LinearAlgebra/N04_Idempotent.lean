import Adam.Metadata

import Adam.Options.MathlibPart

Game "Adam"
World "Module2"
Level 4

Title "Lineare Abbildung"

Introduction
"

"

Statement
""
    {R V : Type _} [Semiring R] [AddCommGroup V] [Module R V]
    (p : V →ₗ[R] V)(h : p ∘ p = p) : LinearMap.ker p ⊓ LinearMap.range p = ⊥ := by
  sorry
  -- rw eq_bot_iff,
  -- intros v hv,
  -- rw submodule.mem_bot,
  -- rw submodule.mem_inf at hv,
  -- cases hv.2 with w hw,
  -- rw ←hw,
  -- rw ←h,
  -- change p (p w) = _,
  -- rw  hw,
  -- rw ←linear_map.mem_ker,
  -- exact hv.1,
