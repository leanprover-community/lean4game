import TestGame.Metadata

import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Real.Basic            -- definiert `ℝ`
import Mathlib.Data.Fin.VecNotation       -- Importiert Matrix/Vektor-Notation
--import Mathlib.LinearAlgebra.FinSupp -- contains `top_le_span_range_iff_forall_exists_fun`
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Finsupp -- default?
import Mathlib.LinearAlgebra.Span

Game "TestGame"
World "Module"
Level 8

Title "Erzeugendensystem"

Introduction
"
Dass eine Familie von Vektoren `M` den ganzen Vektorraum
aufspannt, sagt man in Lean mit `⊤ ≤ span K M`. (Man könnte auch `span K M = ⊤` schreiben,
aber per Konvention wird `≤` bevorzugt, da `x ≤ ⊤` immer gilt (siehe `le_top`))
"

-- notation "ℝ²" => Fin 2 → ℝ

open Submodule Set Finsupp

open BigOperators -- Summen Notation

Statement
  "Zeige, dass `![1, 0], ![1, 1]` den ganzen `ℝ`-Vektorraum `ℝ²` aufspannt."
    : ⊤ ≤ span ℝ (Set.range ![(![1, 0] : Fin 2 → ℝ), ![1, 1]]) := by
  --rw [top_le_span_range_iff_forall_exists_fun]
  sorry
  --   intro v,

  --   use ![v 0 - v 1, v 1],
  --   simp,
  --   funext i,
  --   fin_cases i;
  --   simp,

--NewLemma top_le_span_range_iff_forall_exists_fun le_top
