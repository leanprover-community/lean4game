import Adam.Metadata

import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Parity
import Mathlib.Tactic.Ring

Game "Adam"
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

Statement : 3 ∈ {n : ℕ | Odd n}  := by
  rw [mem_setOf]
  Hint (hidden := true) "**Robo**: Zur Erinnerung, wenn du nicht mehr weisst, wie `Odd` definiert
  ist, benutze `rw [Odd]`."
  Branch
    rw [Odd]
  use 1
  ring

NewLemma Set.mem_setOf
LemmaTab "Set"
