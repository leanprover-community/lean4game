import TestGame.Metadata

import Mathlib.Init.Set
import Mathlib.Tactic.Tauto

set_option tactic.hygienic false

Game "TestGame"
World "SetTheory"
Level 2

Title "leere Menge"

Introduction
"
Gleich wie bei `univ` gibt es leere Mengen `∅` von verschiedenen Typen.
So ist `(∅ : Set ℕ)` in Lean nicht das gleiche wie `(∅ : Set ℤ)`. (`\\empty`)

Zudem hat die Verneinung `¬ (x ∈ A)` die Notation `x ∉ A` (`\\nin`), gleich wie bei `=` and `≠`.

Um zu zeigen, dass etwas nicht in der leeren Menge ist, kannst du wieder `tauto` verwenden.
"

open Set

Statement not_mem_empty
    "Kein Element ist in der leeren Menge enthalten." {A : Type _} (x : A) :
    x ∉ (∅ : Set A) := by
  tauto
