import Adam.Metadata

import Mathlib
import Mathlib.Algebra.Parity
import Mathlib.Tactic.Ring

Game "Adam"
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

Statement :
    ¬Disjoint ({n : ℤ | ∃ k, n = 2 * k} : Set ℤ) ({3, 5, 6, 9, 11} : Set ℤ) := by
  Hint "**Robo**: Öffne als erstes mal `Disjoint`."
  rw [Disjoint]
  Branch
    rw [not_forall] -- why not `push_neg`?
  push_neg
  Hint "**Robo**: Das sieht jetzt ein bisschen gefürchig aus, aber das ist einfach ein `∃`.
  Was du jetzt angeben musst, ist eine Menge, die Teilmenge beider Mengen
  `\{n : ℤ | ∃ k, n = 2 * k}` und `\{3, 5, 6, 9, 11}` ist.
  "
  Hint (hidden := true) "**Robo**: Versuch einmal `use \{6}`."
  use {6}
  Hint "**Robo**: Schau mal wie weit `simp` kommt."
  simp
  use 3
  ring

NewDefinition Disjoint
LemmaTab "Set"
