import TestGame.Metadata

import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.Span

open Submodule

Game "TestGame"
World "Module2"
Level 5

Title "Lineare Abbildung"

Introduction
"
Die interne Summe von Untermodulen wird in Lean mit `⊔` (`\\sup`) geschrieben.
"

Statement
"
Zeige, dass `V₁ ⊔ V₂` tatsächlich die interne Summe `⟨V₁ ∪ V₂⟩` ist.
"
    {K V : Type _} [Field K] [AddCommMonoid V] [Module K V] (V₁ V₂ : Submodule K V) :
    V₁ ⊔ V₂ = span K ( (V₁ : Set V) ∪ V₂ ) := by
  rw [span_union]
  simp
