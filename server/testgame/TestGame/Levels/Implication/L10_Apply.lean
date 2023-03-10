import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Cases
import Mathlib

Game "TestGame"
World "Implication"
Level 10

Title "Lemmas"

Introduction
"
Ihr setzt euch hin und der Gehilfe bringt euch allen Suppe. Neben euch sitzt eine Mechanikerin
über ihre Suppe geneigt.

**Mechanikerin**: Sagt mal, ich hab unten über folgendes tiefgründiges Problem nachgedacht:


Bewiesene Resultate möchte man in späteren Aufgaben als Sätze wieder verwenden.

In Lean sind das Lemmas und Theoreme (wobei es keinen Unterschied zwischen `lemma` und `theorem`
gibt).

Links in der Bibliothek findest du bekannte Lemmas. Wenn das Goal mit der Aussage des Lemmas
übereinstimmt, kannst du es mit `apply [Lemma-Name]` anwenden, wie du das mit Implikationen auch
machst.

Zum Beispiel gibt es ein Lemma, das sagt, dass wenn
$A \\Rightarrow B$ dann $(\\neg A \\lor B)$:

```
lemma not_or_of_imp : (A B : Prop) (h : A → B) :
    ¬A ∨ B := by
  ...
```

Wenn also dein Goal `¬A ∨ B` ist, kannst du mit `apply not_or_of_imp` dieses
Lemma anwenden. Danach musst du noch alle Annahmen zeigen.
"

Statement (A : Prop) : ¬A ∨ A := by
  Hint "**Du**: Das scheint ziemlich offensichtlich.

  **Robo**: Ich glaube, sie will eine detailierte Antwort. Ich kenne ein Lemma
  `not_or_of_imp`, was sagt `(A → B) → ¬ A ∨ B`. Da das Resultat des Lemmas mit
  deinem Goal übreinstimmt, kannst du es mit `apply not_or_of_imp` anwenden."
  apply not_or_of_imp
  Hint (hidden := true) "**Robo**: Ich würd wieder mit `intro` weitermachen."
  intro
  assumption

Conclusion
"
**Mechanikerin**: Danke vielmals, jetzt bin ich schon viel ruhiger.
"

NewLemma not_or_of_imp
DisabledTactic tauto
