import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import TestGame.ToBePorted

Game "TestGame"
World "Contradiction"
Level 2

Title "Suffices"

Introduction
"
Die Taktik `suffices` funktioniert genau gleich wie `have`,
vertauscht aber die beiden Beweisblöcke:

```
suffices h : [Aussage]
[Beweis des Goals (mithilfe von h)]
[Beweis der Aussage h]
```
Auf Deutsch entspricht `suffices g : [Aussage]` dem Ausdruck
\"Es genügt zu zeigen, dass `[Aussage]` wahr ist.\"

Man kann `have` und `suffices` nach belieben vertauschen. Bevorzugt, wählt man es so,
dass der erste Beweisblock der kürzere ist. Zum Beispiel wäre bei der vorigen Aufgabe
`suffices` schöner gewesen:

"

Statement
    "Angenommen, man hat eine Implikation $A \\Rightarrow \\neg B$ und weiss, dass
    $A \\land B$ wahr ist. Zeige, dass dies zu einem Widerspruch führt."
    (A B : Prop) (h : A → ¬ B) (k : A ∧ B) : False := by
  rcases k with ⟨h₁, h₂⟩
  suffices k : ¬ B
  contradiction
  apply h
  assumption

Hint (A : Prop) (B : Prop) (h : A → ¬ B) (k : A ∧ B) : False =>
" Fang mal damit an, das UND in den Annahmen mit `rcases` aufzuteilen.
"

Hint (A : Prop) (B : Prop) (h : A → ¬ B) (k : A) (f : B) : False =>
" Auf Deutsch: \"Es genügt `¬ B` zu zeigen, da dies zu einem direkten Widerspruch führt.\"

  In Lean :

  ```
  suffices k : ¬ B
  contradiction
  [...]
  ```
"

Conclusion ""

NewTactics «suffices»
DisabledTactics «have»

NewLemmas Even Odd not_even not_odd
