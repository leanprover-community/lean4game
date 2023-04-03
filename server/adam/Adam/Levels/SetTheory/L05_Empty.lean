import Adam.Metadata
import Adam.Levels.SetTheory.L04_SubsetEmpty

--import Mathlib.Data.Set.Basic
import Mathlib.Init.Set
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.PushNeg

set_option tactic.hygienic false

Game "Adam"
World "SetTheory"
Level 5

Title "Empty"

Introduction
"
Zeige folgendes Lemma, welches wir gleich brauchen werden:
"

open Set


Statement Set.eq_empty_iff_forall_not_mem
""
    {A : Type _} (s : Set A) :
    s = ∅ ↔ ∀ x, x ∉ s := by
  Hint "Das Lemma `subset_empty_iff` von letzter Aufgabe könnte hilfreich sein."
  rw [←subset_empty_iff]
  rfl -- This is quite a miracle :)

NewTactic constructor intro rw assumption rcases simp tauto trivial
NewLemma Set.subset_empty_iff
LemmaTab "Set"
