import TestGame.Metadata

import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Real.Basic            -- definiert `ℝ`
import Mathlib.Data.Fin.VecNotation       -- Importiert Matrix/Vektor-Notation
--import Mathlib.LinearAlgebra.FinSupp -- contains `top_le_span_range_iff_forall_exists_fun`
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Finsupp -- default?
import Mathlib.LinearAlgebra.Span
import Mathlib

open Submodule

Game "TestGame"
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
