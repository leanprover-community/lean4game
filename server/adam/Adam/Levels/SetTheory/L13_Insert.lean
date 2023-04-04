import Adam.Metadata

import Adam.Options.MathlibPart

Game "Adam"
World "SetTheory"
Level 13

Title "Konkrete Mengen"

Introduction
"
Um zu überprüfen, dass gewisse Elemente in
konkreten Mengen enthalten sind, gibt es nicht direkt eine Taktik, aber ein
einfaches Rezept:

```
simp_rw [mem_insert_iff, mem_singleton_iff] at *
```

vereinfacht Aussagen der Form `6 ∈ {0, 6, 1}` zu `(6 = 0) ∨ (6 = 6) ∨ (6 = 1)`,
und dann kann `tauto` diese Aussage beweisen.

Bei `⊆` kann man wie schon vorher zuerst mit `intro x hx` die Definition
auseinandernehmen und dann gleich vorgehen.

"

open Set

Statement :
    ({2, 3, 5} : Set ℕ) ⊆ {4, 2, 5, 7, 3} := by
  Hint "Fang wieder mit `rw [subset_def]` oder direkt mit `intro` an."
  intro x hx
  simp_rw [mem_insert_iff, mem_singleton_iff] at *
  tauto

NewLemma Set.mem_insert_iff Set.mem_singleton_iff
LemmaTab "Set"
