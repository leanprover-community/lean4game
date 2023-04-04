import Adam.Metadata

import Adam.Options.MathlibPart

Game "Adam"
World "SetTheory"
Level 10

Title "Morgansche Regeln"

Introduction
"
Die De-Morgan'schen Regeln sagen `(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ`
und `(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ` sind in Lean als

`compl_union` und `compl_inter`.


Zudem gibt es die Lemmas `mem_compl_iff : x ∈ Aᶜ ↔ x ∉ A` und
`not_mem_compl_iff`, mit welchen
man die de-Morganschen Regeln einfach selber beweisen könnten.


Die meisten Aufgaben über Mengen sind eine Kombination von `rw` und `simp_rw` verschiedenster
NewLemma in `import Mathlib.Data.Set`.

Die Taktik `simp_rw` funktioniert ähnlich wie `rw`, aber sie versucht jedes Lemma so oft
wie möglich anzuwenden. Wir kennen also 4 etwas verwandte Optionen um Lemmas und Theoreme zu
brauchen:

- `rw [lemma_A, lemma_B]`: führt jedes Lemma genau einmal aus in der Reihenfolge.
- `simp_rw [lemma_A, lemma_B]` : führt jedes Lemma in Reihenfolge so oft aus wie möglich.
- `simp only [lemma_A, lemma_B]` : sucht eine Kombination der beiden Lemmas, ohne bestimmte
                                   Reihenfolge.
- `simp [lemma_A, lemma_B]` : Braucht die beiden Lemmas und alle simp-Lemmas.
"

open Set

#check compl_union
#check compl_inter
#check mem_compl_iff

Statement
    (A B C : Set ℕ) : (A \ B)ᶜ ∩ (C \ B)ᶜ = ((univ \ A) \ C) ∪ (univ \ Bᶜ) := by
  Hint "Oft kann es auch nützlich sein, mit `rw [← …]` rückwärts umzuschreiben.
  Der ganze Level ist mit `rw`/`simp_rw` und den Lemmas in deiner Bibliothek
  lösbar."
  rw [←compl_union]
  rw [←union_diff_distrib]
  rw [diff_diff]
  simp_rw [←compl_eq_univ_diff]
  rw [←compl_inter]
  rw [diff_eq_compl_inter]
  rw [inter_comm]

OnlyTactic rw simp_rw tauto trivial assumption rfl «have» «suffices»
NewTactic simp_rw
LemmaTab "Set"
NewLemma Set.mem_compl_iff Set.compl_union Set.diff_diff Set.compl_inter
  Set.diff_eq_compl_inter Set.inter_comm
