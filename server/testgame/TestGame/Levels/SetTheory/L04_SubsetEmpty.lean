import TestGame.Metadata
import TestGame.Levels.SetTheory.L03_Subset

import Mathlib.Init.Set
import Mathlib.Tactic.Tauto

set_option tactic.hygienic false

Game "TestGame"
World "SetTheory"
Level 4

Title "Teilmengen"

Introduction
"
Ein zentrales Lemma ist `Subset.antisymm_iff` welches folgendes sagt:

```
A = B ↔ A ⊆ B ∧ B ⊆ A
```

Fast immer wenn man Gleichheiten von Mengen zeigen muss, will man diese in zwei Ungleichungen
aufteilen.
"

namespace MySet

open Set

-- Copied some lemmas from `Matlib.Data.Set.Basic` in order to not import the entire file.
theorem tmp {α : Type _} {s t : Set α} : s = t → s ⊆ t :=
  fun h₁ _ h₂ => by rw [← h₁] ; exact h₂

theorem Subset.antisymm_iff {α : Type _} {a b : Set α} : a = b ↔ a ⊆ b ∧ b ⊆ a :=
  ⟨fun e => ⟨tmp e, tmp e.symm⟩, fun ⟨h₁, h₂⟩ => Set.ext fun _ => ⟨@h₁ _, @h₂ _⟩⟩

@[simp]
theorem empty_subset {α : Type _} (s : Set α) : ∅ ⊆ s :=
  fun.

Statement subset_empty_iff
"Die einzige Teilmenge der leeren Menge ist die leere Menge."
    {A : Type _} (s : Set A) :
    s ⊆ ∅ ↔ s = ∅ := by
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

Tactics constructor intro rw assumption rcases simp tauto trivial

Lemmas Subset.antisymm_iff empty_subset

end MySet
