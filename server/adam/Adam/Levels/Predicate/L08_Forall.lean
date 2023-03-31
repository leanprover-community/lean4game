import Adam.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import Mathlib.Algebra.Parity
import Mathlib

set_option tactic.hygienic false

Game "Adam"
World "Predicate"
Level 8

Title "Für alle"

Introduction
"
Nach längerem Durcheinander findet ein weiteres Blatt aus der Menge zu Euch.
"

--   Zum `∃` gehört auch das \"für alle\" `∀` (`\\forall`).

-- Der Syntax ist `∀ (n : ℕ), 0 ≤ n` also wie beim `∃` trennt ein Komma die Annahmen von der Aussage.

-- Eine `∀`-Aussage in den Annahmen verhält sich so wie ein Lemma. Das heisst man kann
-- auch diese mit `apply` und `rw` anwenden, je nachdem was die Aussage nach dem Komma ist.

-- Also folgende Annahme und Lemma sind genau :
-- - `(le_square : ∀ (n : ℕ), n ≤ n^2)`
-- - `lemma le_square (n : ℕ) : n ≤ n^2`

-- Ein `∀` im Goal kann man mit `intro` angehen, genau wie bei einer Implikation `→`.


-- TODO: 1-2 Aufgaben mehr.

Statement : ∀ (x : ℕ), (Even x) → Odd (1 + x) := by
  Hint "**Du**: Das `∀` heisst sicher \"für alle\".

  **Robo**: Und man schreibt `\\forall`. Ein `∀ x, …` im Beweisziel kannst du wie eine
  Implikation mit `intro x` angehen."
  intro x h
  unfold Even at h
  unfold Odd
  rcases h with ⟨y, hy⟩
  use y
  rw [hy]
  ring

Conclusion "Wieder werdet Ihr mit einem Applaus belohnt, und die Formalosophinnen beratschlagen sich, was sie Euch noch vorlegen wollen."
