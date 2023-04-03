import Adam.Metadata
import Adam.Levels.SetTheory.L05_Empty

import Mathlib.Data.Set.Basic

set_option tactic.hygienic false

Game "Adam"
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

Statement Set.nonempty_iff_ne_empty
    {A : Type _} (s : Set A) :
    s.Nonempty ↔ s ≠ ∅ := by
  Hint "Am besten fängst du mit `unfold Set.Nonempty` an."
  unfold Set.Nonempty
  Hint "Mit `ne_eq` und `eq_empty_iff_forall_not_mem` kannst du hier weiterkommen."
  rw [ne_eq, eq_empty_iff_forall_not_mem]
  Hint (hidden := true) "`push_neg` kann hier helfen."
  push_neg
  rfl

NewLemma ne_eq Set.eq_empty_iff_forall_not_mem
NewDefinition Set.Nonempty
LemmaTab "Set"
