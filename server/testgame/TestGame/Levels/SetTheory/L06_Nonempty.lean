import TestGame.Metadata
import TestGame.Levels.SetTheory.L05_Empty

import Mathlib.Data.Set.Basic

set_option tactic.hygienic false

Game "TestGame"
World "SetTheory"
Level 6

Title "Nonempty"

Introduction
"
Das Gegenteil von `A = ∅` ist `A ≠ ∅`, aber in Lean wird der Ausdruck `A.Nonempty` bevorzugt.
Dieser ist dadurch existiert, dass in `A` ein Element existiert: `∃x, x ∈ A`.

Zeige dass die beiden Ausdrücke äquivalent sind:
"

open Set

Statement nonempty_iff_ne_empty
""
    {A : Type _} (s : Set A) :
    s.Nonempty ↔ s ≠ ∅ := by
  rw [Set.Nonempty]
  rw [ne_eq, eq_empty_iff_forall_not_mem]
  push_neg
  rfl

NewTactic constructor intro rw assumption rcases simp tauto trivial

NewLemma Subset.antisymm_iff empty_subset
