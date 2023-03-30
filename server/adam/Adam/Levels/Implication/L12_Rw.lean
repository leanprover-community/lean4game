import Adam.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Cases
import Mathlib.Logic.Basic

Game "Adam"
World "Implication"
Level 12

Title "Lemmas"

Introduction
"
**Operationsleiter**:  Wieder etwas für den Kollegen ….  Und er wollte wieder einen Beweise ohne `apply`.  Ich sehe hier auch, dass ich mir schon einmal etwas hierzu notiert hatte.  Richtig, es gibt da dieses Lemma:
```
lemma not_not (A : Prop) : ¬¬A ↔ A
```

**Operationsleiter**:  Schafft Ihr das damit?
"

Statement (A B C : Prop) : (A ∧ (¬¬C)) ∨ (¬¬B) ∧ C ↔ (A ∧ C) ∨ B ∧ (¬¬C) := by
  Hint "**Robo**: Ein Lemma, das wie `not_not` ein `↔` oder `=` im Statement hat, kann
  auch mit `rw [not_not]` verwendet werden."
  rw [not_not]
  Hint "**Du**: Häh, wieso hat das jetzt 2 von 3 der `¬¬` umgeschrieben?

  **Robo**: `rw` schreibt nur das erste um, das es findet, also `¬¬C`. Aber weil dieses
  mehrmals vorkommt, werden die alle ersetzt …

  **Du**: Ah, und `¬¬B` ist etwas anderes, also brauche ich das Lemma nochmals."
  rw [not_not]

Conclusion
"
**Du**: Wir sind schon fertig …?

**Robo**: Ja, `rw` versucht immer anschließend `rfl` aufzurufen, und das hat hier funktioniert.
"

DisabledTactic tauto apply
NewLemma Classical.not_not
LemmaTab "Logic"
