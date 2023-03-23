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
Level 6

Title "Hülle"

Introduction
"
Ein typischer Untervektorraum ist die Hülle `⟨M⟩`, oder `span`, also die Menge aller
`K`-Linearkombinationen von Elementen aus der Menge `M`.

In Lean ist dies `Submodule.span K M`.

"

local notation "ℝ²" => Fin 2 → ℝ

open Submodule Set Finsupp

Statement mem_span_of_mem
  "Zeige, dass $x \\in M$ auch Element von der $K$-linearen Hülle
  \\langle M \\rangle ist."
    {V K : Type _} [Field K] [AddCommMonoid V]
    [Module K V] (M : Set V) {x : V} (h : x ∈ M) :
    x ∈ span K M := by
  rw [mem_span]
  intro p hp
  specialize hp h
  assumption
