import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import Mathlib.Algebra.Parity
import Mathlib

Game "TestGame"
World "Predicate"
Level 7

Title "Für alle"

Introduction
"
Zum `∃` gehört auch das \"für alle\" `∀` (`\\forall`).

Der Syntax ist `∀ (n : ℕ), 0 ≤ n` also wie beim `∃` trennt ein Komma die Annahmen von der Aussage.

Eine `∀`-Aussage in den Annahmen verhält sich so wie ein Lemma. Das heisst man kann
auch diese mit `apply` und `rw` anwenden, je nachdem was die Aussage nach dem Komma ist.

Also folgende Annahme und Lemma sind genau :
- `(le_square : ∀ (n : ℕ), n ≤ n^2)`
- `lemma le_square (n : ℕ) : n ≤ n^2`

Ein `∀` im Goal kann man mit `intro` angehen, genau wie bei einer Implikation `→`.


TODO: 1-2 Aufgaben mehr.
"

Statement
    " Für alle natürlichen Zahlen $x$ gilt, falls $x$ gerade ist, dann ist $x + 1$
    ungerade." : ∀ (x : ℕ), (Even x) → Odd (1 + x) := by
  intro x h
  unfold Even at h
  unfold Odd
  rcases h with ⟨y, hy⟩
  use y
  rw [hy]
  ring

Hint (n : ℕ) (hn : Odd n) (h : ∀ (x : ℕ), (Odd x) → Even (x + 1)) : Even (n + 1) =>
"`∀ (x : ℕ), (odd x) → even (x + 1)` ist eigentlich das gleiche wie
`(x : ℕ) → `"

Conclusion "Für-alle-Statements, Implikationen und Lemmas/Theoreme verhalten sich alle
praktisch gleich. Mehr dazu später."

Tactics ring intro unfold
