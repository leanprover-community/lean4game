import TestGame.Metadata

import Mathlib
import Mathlib.Algebra.Parity
import Mathlib.Tactic.Ring

Game "TestGame"
World "SetTheory2"
Level 3

Title ""

Introduction
"
Um anzunehmen, dass zwei Mengen disjunkt sind schreibt man
`Disjoint S T`, welches dadurch definiert ist das die
einzige gemeinsame Teilmenge die leere Menge ist,
also etwa `A ⊆ S → A ⊆ T → A ⊆ ∅`.

Beachte, dass `Disjoint` in Lean genereller definiert ist als
für Mengen, deshalb siehst du die Symbole
`≤` anstatt `⊆` und `⊥` anstatt `∅`, aber diese bedeuten genau
das gleiche.
"

open Set

Statement
"" :
    ¬Disjoint ({n : ℤ | ∃ k, n = 2 * k} : Set ℤ) ({3, 5, 6, 9, 11} : Set ℤ) := by
  unfold Disjoint
  rw [not_forall] -- why not `push_neg`?
  use {6}
  simp
  use 3
  ring


NewTactic constructor intro rw assumption rcases simp tauto trivial
