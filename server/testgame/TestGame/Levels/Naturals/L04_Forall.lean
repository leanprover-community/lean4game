import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import TestGame.ToBePorted

Game "TestGame"
World "Nat"
Level 4

Title "Für alle"

Introduction
"
Zum `∃` gehört auch das \"für alle\" `∀` (`\\forall`).

Ein `∀` im Goal kann man mit `intro` angehen, genau wie bei einer Implikation `→`.
"

Statement
    " Für alle natürlichen Zahlen $x$ gilt, falls $x$ gerade ist, dann ist $x + 1$
    ungerade." : ∀ (x : ℕ), (even x) → odd (1 + x) := by
  intro x h
  unfold even at h
  unfold odd
  rcases h with ⟨y, hy⟩
  use y
  rw [hy]
  ring

Message (n : ℕ) (hn : odd n) (h : ∀ (x : ℕ), (odd x) → even (x + 1)) : even (n + 1) =>
"`∀ (x : ℕ), (odd x) → even (x + 1)` ist eigentlich das gleiche wie
`(x : ℕ) → `"

Conclusion "Für-alle-Statements, Implikationen und Lemmas/Theoreme verhalten sich alle
praktisch gleich. Mehr dazu später."

Tactics ring intro unfold
