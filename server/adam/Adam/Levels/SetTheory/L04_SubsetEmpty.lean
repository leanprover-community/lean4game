import Adam.Metadata
import Adam.Levels.SetTheory.L03_Subset

import Mathlib.Init.Set
import Mathlib.Tactic.Tauto
import Mathlib

set_option tactic.hygienic false

Game "Adam"
World "SetTheory"
Level 4

Title "Teilmengen"

Introduction
"
Etwas weiter kommt ihr an einem kleinen Gemüsestand vorbei. Da ihr nicht so
richtig einen Plan habt, fragt ihr den Verkäufer.

**Verkäufer**: Hier ist was ganz wichtiges, was ihr noch oft brauchen werdet:
Ein zentrales Lemma ist `Subset.antisymm_iff` welches folgendes sagt:

```
lemma antisymm_iff {α : Type} {A B : Set α} : A = B ↔ A ⊆ B ∧ B ⊆ A
```

Fast immer wenn man Gleichheiten von Mengen zeigen muss, will man diese in zwei Ungleichungen
aufteilen.
"

namespace MySet

open Set Subset

-- Copied some lemmas from `Matlib.Data.Set.Basic` in order to not import the entire file.
theorem tmp {α : Type _} {s t : Set α} : s = t → s ⊆ t :=
  fun h₁ _ h₂ => by rw [← h₁] ; exact h₂

theorem Subset.antisymm_iff {α : Type _} {a b : Set α} : a = b ↔ a ⊆ b ∧ b ⊆ a :=
  ⟨fun e => ⟨tmp e, tmp e.symm⟩, fun ⟨h₁, h₂⟩ => Set.ext fun _ => ⟨@h₁ _, @h₂ _⟩⟩

@[simp]
theorem empty_subset {α : Type _} (s : Set α) : ∅ ⊆ s :=
  fun.

Statement subset_empty_iff {A : Type _} (s : Set A) :
    s ⊆ ∅ ↔ s = ∅ := by
  Hint "**Du**: Ja, die einzige Teilmenge der leeren Menge ist die leere Menge.
  Das ist doch eine Tautologie?

  **Robo**: Ja schon, aber zuerst einmal explizit."
  Hint (hidden := true) "**Robo**: Fang doch einmal mit `constructor` an."
  constructor
  intro h
  Hint "**Robo**: "
  apply Subset.antisymm
  assumption
  simp only [empty_subset]
  intro a
  rw [Subset.antisymm_iff] at a
  rcases a with ⟨h₁, h₂⟩
  assumption

DisabledTactic tauto
NewLemma Subset.antisymm Subset.antisymm_iff empty_subset

end MySet
