import Adam.Metadata

import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Span

Game "Adam"
World "Module2"
Level 7

Title "Lineare Abbildung"

Introduction
"
Die externe Summe von (Unter-) Modulen wird als `V × W` geschrieben
Das Produkt zweier Module wird mit `×` geschrieben.

Lean weiss dann automatisch, dass das Produkt wieder ein Vektorraum ist.
-/
example : module ℝ (ℝ × ℝ) := infer_instance

/-
Und `ℝ × ℝ` und `fin 2 → ℝ` sind natürlich Isomorph. In Praxis eignet sich
die Funktionsschreibweise besser, deshalb verwenden wir diese als
definition für `ℝ²`.

Hier die Äquivalenz als generelle Typen:
-/
example : (fin 2 → ℝ) ≃ ℝ × ℝ  :=
begin
  apply pi_fin_two_equiv,
end

/-
Äquivalenz als Vektorräume schreibt man als `ℝ`-lineare Äquivalenz `≃ₗ[ℝ]`.
"

Statement
"Zeige dass das Produkt `ℝ × ℝ` und `ℝ²` isomorph sind als `ℝ`-Vektorräume."
    : ((Fin 2) → ℝ) ≃ₗ[ℝ] ℝ × ℝ := by
  sorry
