import Adam.Metadata

import Adam.Options.MathlibPart

open Submodule

Game "Adam"
World "Module2"
Level 2

Title "Lineare Abbildung"

Introduction
"
  (Verpackungswahn)
If `f` is a function and `M` a subset of its domain, then
`f '' M` or `set.image f M` is the notation for the image, which is
usally denoted `f(M) = {y | ∃ x ∈ M, f(x) = y}` in mathematical texts.
"

-- TODO: This is blocked by
-- https://github.com/leanprover/lean4/issues/2074

set_option autoImplicit false
-- set_option pp.all true

Statement
"" : True := by
  sorry

-- example {K V W : Type} [Field K] [AddCommMonoid V] [AddCommMonoid W]
--     [Module K V] [Module K W] (M : Set V) (f : V →ₗ[K] W) :
--   f '' span K M = @span K (f '' M) := by
--   sorry

-- example {K V : Type} [Field K] [AddCommMonoid V]
--     [Module K V] (M : Set V) (f : V →ₗ[K] V) : f '' M = f '' M =  := by
--   rfl
