import Adam.Metadata

import Adam.Options.MathlibPart

Game "Adam"
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
