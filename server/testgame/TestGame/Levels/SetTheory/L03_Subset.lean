import TestGame.Metadata

import Mathlib.Init.Set
import Mathlib.Tactic.Tauto

set_option tactic.hygienic false

Game "TestGame"
World "SetTheory"
Level 3

Title "Teilmengen"

Introduction
"
Hat man zwei Mengen `(A B : Set ℕ)` kann man fragen, ob diese Teilmengen
voneinander sind: `A ⊆ B` (`\\sub`/`\\ss`) ist die Notation für Teilmengen, die auch gleich
sein können.

`A ⊆ B` ist als `∀ x, x ∈ A → x ∈ B` definiert, das heisst, ein `⊆` kann immer auch mit `intro x hx`
angegangen werden.

Die Taktik `tauto` macht das automatisch, aber um dies zu lernen ist `tauto` hier deaktiviert.
Benutze also `intro`:
"

namespace MySet

open Set

theorem mem_univ {A : Type _} (x : A) : x ∈ (univ : Set A) := by
  trivial

theorem not_mem_empty {A : Type _} (x : A) : x ∉ (∅ : Set A) := by
  tauto

Statement subset_empty_iff
"." (A : Set ℕ) : A ⊆ univ := by
  intro h hA
  apply mem_univ -- or `trivial`.

Tactics intro trivial apply
-- blocked: tauto simp

end MySet
