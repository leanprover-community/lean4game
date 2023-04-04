import Adam.Metadata

import Adam.Options.MathlibPart


Game "Adam"
World "SetTheory2"
Level 5

Title ""

Introduction
"
Zu der Teilmengen-Schreibweise (`SetOf`) gibt es noch zwei spezielle
Syntax, die abundzu auftreten.

Der erste ist `{ x ∈ S | 0 ≤ x}` ( für z.B `(S : Set ℤ)`),
welcher eine Abkürzung für `{ x : ℤ | x ∈ S ∧ 0 ≤ x}` ist.
Entsprechend hilft auch hier `setOf_and`.

"

open Set

Statement
"" (S : Set ℤ) :
    { x ∈ (S : Set ℤ) | 0 ≤ x} ⊆ S := by
  simp

LemmaTab "Set"
