import TestGame.Metadata

import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib

Game "TestGame"
World "Basis"
Level 4

Title "Basis"

namespace Ex_Basis

scoped notation "ℝ²" => Fin 2 → ℝ

open Submodule

Introduction
"

"

lemma exercise1 : LinearIndependent ℝ ![(![1, 0] : ℝ²), ![1, 1]] := sorry

lemma exercise2 :  ⊤ ≤ span ℝ (Set.range ![(![1, 0] : Fin 2 → ℝ), ![1, 1]]) := sorry

Statement : Basis (Fin 2) ℝ ℝ² := by
  apply Basis.mk
  apply exercise1
  apply exercise2

end Ex_Basis
