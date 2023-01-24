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

Statement
"Benutze `not_or_of_imp` um zu zeigen, dass $\\neg A \\lor A$ wahr ist."
    (A : Prop) : ¬A ∨ A := by
  apply not_or_of_imp
  intro
  assumption

HiddenHint (A : Prop) :  ¬A ∨ A =>
"Das Lemma wendest du mit `apply not_or_of_imp` an."

HiddenHint (A : Prop) : A → A =>
"Wie immer, `intro` ist dein Freund."

Conclusion
"
"

Tactics apply left right assumption

Lemmas not_or_of_imp
