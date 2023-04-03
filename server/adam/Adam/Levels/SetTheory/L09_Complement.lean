import Adam.Metadata

import Mathlib.Data.Set.Basic

Game "Adam"
World "SetTheory"
Level 9

Title "Komplement"

Introduction
"
Das Komplement einer Menge wird als `Aᶜ` (`\\^c`) geschrieben. Wichtige Lemmas
sind `not_mem_compl_iff` und `compl_eq_univ_diff`.
"

open Set

Statement
""
    (A : Set ℕ) (h : Aᶜ ⊆ A) : A = univ := by
  Hint "Start doch mit `apply Subset.antisymm`."
  apply Subset.antisymm
  simp only [subset_univ]
  Hint "Da `⊆` als `∀x, x ∈ A → x ∈ B ` definiert ist, fängst du
  am besten mit `intro` an."
  intros x hx
  Hint "Eine Möglichkeit ist, eine Fallunterscheidung zu machen: `by_cases g: {x} ∈ {A}ᶜ`."
  by_cases h4 : x ∈ Aᶜ
  Hint "Hier könnte `mem_of_subset_of_mem` hilfreich werden."
  apply mem_of_subset_of_mem h
  assumption
  Hint "Diese Richtung geben wir als Lemma: `not_mem_compl_iff`."
  rw [not_mem_compl_iff] at h4
  assumption

NewTactic constructor intro rw assumption rcases simp tauto trivial
NewLemma Set.not_mem_compl_iff Set.mem_of_subset_of_mem Set.compl_eq_univ_diff
DisabledTactic tauto
LemmaTab "Set"
