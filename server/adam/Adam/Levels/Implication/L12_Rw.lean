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
Der Arbeitskollegin der Mechanikerin, der die ganze Zeit gespannt zugehört hat, dreht sich zu
euch.

Er ist offensichtlich interessiert and existierenden Resultaten zu sein, aber offenbar
kann er nicht viel mit `apply` anfangen.

Er hat aber folgendes Resultat bereit:

```
lemma not_not (A : Prop) : ¬¬A ↔ A
```

und stellt euch folgende Frage:
"

Statement (A B C : Prop) : (A ∧ (¬¬C)) ∨ (¬¬B) ∧ C ↔ (A ∧ C) ∨ B ∧ (¬¬C) := by
  Hint "**Robo**: Ein Lemma, das wie `not_not` ein `↔` oder `=` im Statement hat, kann
  auch mit `rw [not_not]` verwendet werden."
  rw [not_not]
  Hint "**Du**: Häh, wieso hat das jetzt 2 von 3 der `¬¬` umgeschrieben?

  **Robo**: `rw` schreibt nur das erste um, das es findet, also `¬¬C`. Aber weil dieses
  mehrmals vorkommt, werden die alle ersetzt…

  **Du**: Ah, und `¬¬B` ist was anderes, also brauch ich das Lemma nochmals."
  rw [not_not]

Conclusion
"
**Du**: Ah und wir sind fertig…?

**Robo**: Ja, `rw` versucht immer anschliessend `rfl` aufzurufen, und das hat hier
funktioniert.
"

DisabledTactic tauto apply
NewLemma not_not
