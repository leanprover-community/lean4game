import Adam.Metadata

import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Parity
import Mathlib.Tactic.Ring

import Adam.ToBePorted

Game "Adam"
World "SetTheory2"
Level 2

Title "Potenzmenge"

Introduction
"
Eine andere wichtige Menge ist die Potenzmenge einer Menge, welche als
`𝒫 A` geschrieben wird (`\\powerset`). Diese ist als `{S | S ⊆ A}` definiert, also
alle Mengen, die in $A$ enthalten sind.

Eines der wichtigsten Lemmas ist `mem_powerset_iff: x ∈ 𝒫 s ↔ x ⊆ s` welches
im Grunde die Definition einsetzt.
"

open Set

Statement
"" (X Y : Set ℕ):
    𝒫 X ∪ 𝒫 Y ⊆ 𝒫 (X ∪ Y)  := by
  Hint "**Robo**: Fang mal mit `intro` an, wie das bei `⊆` fast immer der Fall ist."
  intro A hA
  Hint "**Robo**: Als nächstes must du noch die Annahme `{A} ∈ 𝒫 X ∪ 𝒫 Y` zu
  `{A} ∈ (𝒫 X) ∨ {A} ∈ (𝒫 Y)` wechseln. Dafür kennst du schon ein Lemma."
  rw [mem_union] at hA
  Hint "**Robo**: Jetzt wär der Zeitpunkt um `mem_powerset_iff` mal überall anzuwenden."
  simp_rw [mem_powerset_iff] at *
  Hint "**Robo**: Jetzt kann `tauto` den rest übernehmen, vielleicht solltest du diese
  Hilfe annehmen.
  Wenn nicht, brauchst du vermutlich die Lemmas `Set.subset_union_of_subset_left`
  und `Set.subset_union_of_subset_right`"
  Branch
    rcases hA with hA | hA
    apply subset_union_of_subset_left
    assumption
    apply subset_union_of_subset_right
    assumption
  tauto

NewLemma Set.mem_powerset_iff Set.subset_union_of_subset_left Set.subset_union_of_subset_right
LemmaTab "Set"
