import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Cases
import Mathlib.Logic.Basic

Game "TestGame"
World "Implication"
Level 11

Title "Lemmas"

Introduction
"
Wenn die Aussage eines Lemmas eine Äquivalenz ist, kann man dieses auch mit `rw` brauchen,
wie du es von Äquivalenzen kennst.

Ein wichtiges Lemma ist dass $\\neg(\\neg A))$ und $A$ äquivalent sind:

```
lemma not_not (A : Prop) : ¬¬A ↔ A := by
  ...
```

Mit `rw [not_not]` sucht Lean also im Goal ein Term `¬¬(·)` und entfernt dort das `¬¬`.
"

Statement
"Zeige, dass $A ∨ (¬¬B) ∧ C$ und $A ∨ B ∧ C$ äquivalent sind."
    (A B C : Prop) : A ∨ (¬¬B) ∧ C ↔ A ∨ B ∧ C := by
  rw [not_not]

Conclusion
"
`rw` hat automatisch `rfl` ausgeführt und dadurch den Beweis beendet.
"

NewTactics rw

NewLemmas not_not not_or_of_imp
