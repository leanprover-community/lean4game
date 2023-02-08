import TestGame.Metadata
import TestGame.Levels.SetTheory.L04_SubsetEmpty

--import Mathlib.Data.Set.Basic
import Mathlib.Init.Set
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.PushNeg

set_option tactic.hygienic false

Game "TestGame"
World "SetTheory"
Level 5

Title "Nonempty"

Introduction
"
Das Gegenteil von `A = ∅` ist `A ≠ ∅`, aber in Lean wird der Ausdruck `A.Nonempty` bevorzugt.
Dieser ist dadurch existiert, dass in `A` ein Element existiert: `∃x, x ∈ A`.

Zeige dass die beiden Ausdrücke äquivalent sind:
"

namespace MySet

open Set

theorem subset_empty_iff {A : Type _} (s : Set A) : s ⊆ ∅ ↔ s = ∅ := by
  constructor
  intro h
  rw [Subset.antisymm_iff]
  constructor
  assumption
  simp only [empty_subset]
  intro a
  rw [Subset.antisymm_iff] at a
  rcases a with ⟨h₁, h₂⟩
  assumption

Statement eq_empty_iff_forall_not_mem
""
    {A : Type _} (s : Set A) :
    s = ∅ ↔ ∀ x, x ∉ s := by
  rw [←subset_empty_iff]
  rfl -- This is quite a miracle :)

NewTactics constructor intro rw assumption rcases simp tauto trivial

NewLemmas Subset.antisymm_iff empty_subset

end MySet
