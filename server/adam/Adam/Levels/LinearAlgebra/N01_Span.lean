import TestGame.Metadata

import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Real.Basic            -- definiert `ℝ`
import Mathlib.Data.Fin.VecNotation       -- Importiert Matrix/Vektor-Notation
--import Mathlib.LinearAlgebra.FinSupp -- contains `top_le_span_range_iff_forall_exists_fun`
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Finsupp -- default?
import Mathlib.LinearAlgebra.Span

Game "TestGame"
World "Module2"
Level 1

open Submodule

-- Verpackungswahn 1a)
Title "Verpackungswahn"

Introduction
"

"

Statement
""
    {K V : Type _} [Field K] [AddCommMonoid V] [Module K V] (M : Set V) :
    span K ↑(span K M) = span K M := by
  apply Submodule.span_eq
  -- or : simp
