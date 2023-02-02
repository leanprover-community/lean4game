import TestGame.Metadata

import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Parity
import Mathlib.Tactic.Ring

Game "TestGame"
World "SetTheory2"
Level 1

Title "Mengen mit Konditionen"

Introduction
"
Eine wichtige mathematische Notation ist Teilmengen zu erstellen,
die gewissen Bedingungen unterliegen.

`{n : ℕ | Odd n}` ist die Menge aller natürlichen Zahlen, die ungerade sind.
Diese Konstruktion hat in Lean den Namen `setOf`

Um zu beweisen, dass ein Element in einer Teilmenge mit Bedingungen ist, braucht
man `rw [mem_setOf]`. Danach muss man zeigen, dass die Bedinung für
dieses Element erfüllt ist.
"

open Set

Statement
"" :
    3 ∈ {n : ℕ | Odd n}  := by
  rw [mem_setOf]
  use 1
  ring

Tactics constructor intro rw assumption rcases simp tauto trivial

Lemmas Subset.antisymm_iff empty_subset
