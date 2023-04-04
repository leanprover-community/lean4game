import Adam.Metadata

import Adam.Options.MathlibPart

set_option tactic.hygienic false

Game "Adam"
World "SetTheory"
Level 8

Title "Schnittmenge und Vereinigung"

Introduction
"
Ansonsten gibt es jegliche Lemmas in der Mathlib
die beim Umgang mit diesen Operationen weiterhelfen. Schaue in der Bibliothek auf
der Seite nach Lemmas, die dir hier weiterhelfen!

Denk daran, die lemma Namen sind blockweise aus der Aussage konstruiert. Ein lemma mit
der Aussage `C \\ (A ∩ B) + …` wird vermutlich mit `diff_inter_…` anfangen.
"

open Set

Statement
""
    (A B : Set ℕ) : univ \ (A ∩ B) = (univ \ A) ∪ (univ \ B) ∪ (A \ B) := by
  rw [diff_inter]
  Hint (hidden := true) "mit `union_assoc` und `union_diff_distrib` kannst du
  auf der rechten Seite weiterkommen."
  rw [union_assoc]
  rw [←union_diff_distrib]
  rw [univ_union]

NewTactic constructor intro rw assumption rcases simp tauto trivial
DisabledTactic tauto
NewLemma Set.diff_inter Set.union_assoc Set.union_diff_distrib Set.univ_union
LemmaTab "Set"

Conclusion "Wie du vielleicht bemerkt hast, könnte `tauto` sowas automatisch lösen."
