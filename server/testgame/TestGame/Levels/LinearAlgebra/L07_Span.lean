import TestGame.Metadata

import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Real.Basic            -- definiert `ℝ`
import Mathlib.Data.Fin.VecNotation       -- Importiert Matrix/Vektor-Notation
--import Mathlib.LinearAlgebra.FinSupp -- contains `top_le_span_range_iff_forall_exists_fun`
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Finsupp -- default?
import Mathlib.LinearAlgebra.Span
import Mathlib.Tactic.LibrarySearch
import Mathlib

Game "TestGame"
World "Module"
Level 7

Title "Hülle"

Introduction
"
"

-- notation "ℝ²" => Fin 2 → ℝ

open Submodule Set Finsupp

open BigOperators -- Summen Notation

-- TODO: Why is this not in Mathlib?
lemma mem_span_of_mem {V K : Type _} [Field K] [AddCommMonoid V]
    [Module K V] (M : Set V) {x : V} (h : x ∈ M) :
    x ∈ span K M := by
  rw [mem_span]
  intro p hp
  specialize hp h
  assumption

Statement
  "Für $x, y \\in M$, zeige dass $x + 2y$ in der $K$-linearen Hülle $\\langle M \\rangle$ liegt."
    {V K : Type _} [Field K] [AddCommMonoid V] [Module K V] (M : Set V) {x y : V}
    (h₁ : x ∈ M) (h₂ : y ∈ M) :
    x + (2 : K) • y ∈ span K M := by
  apply add_mem
  apply mem_span_of_mem
  assumption
  apply smul_mem
  apply mem_span_of_mem
  assumption
