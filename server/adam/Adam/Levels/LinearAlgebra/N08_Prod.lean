import TestGame.Metadata

import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Span

universe u

Game "TestGame"
World "Module2"
Level 8

Title "Lineare Abbildung"

Introduction
"
Eine Familie von Vektorräumen schreibt man erst einmal als Funktion einer Indexmenge `ι`.
-/

variables {ι : Type u} {V : ι → Type u}

/-
Für einen einzelnen Vektorraum würde man jetzt Instanzen `[add_comm_monoid V] [module K V]`
definieren. Lean-Instanzen-Manager versteht hier `∀`-Ausdrücke:
-/

variables [∀i, add_comm_monoid (V i)] [∀i, module K (V i)]

/-
Ein externes Produkt von Vektorräumen schreibt man einfach mit `\\Pi`, also `Π i, V i`.

Lean kann aus den Ausdrücken oben dann automatisch herausfinden, dass `Π i, V i`
ein `K`-Vektorraum ist:
"

Statement
"Sei `U` ein `K`-Vektorraum und `fᵢ : U → Vᵢ` eine Familie von `K`-lineare Abbildungen
in `K`-Vektorräume. Dann gibt es genau eine Abbildung `f : U → (Π i, V i)`, die mit
allen kommutiert."
    {K U : Type u} [Field K] {ι : Type u} {V : ι → Type u}
    [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
    [AddCommMonoid U] [Module K U]
    (f : ∀ i, U →ₗ[K] (V i)) : U →ₗ[K] (∀ i, V i) := by
  sorry
-- { to_fun := λv i, f i v,
--   map_add' :=
--   begin
--     intros,
--     funext,
--     simp,
--   end,
--   map_smul' :=
--   begin
--     intros,
--     funext,
--     simp,
--   end }
