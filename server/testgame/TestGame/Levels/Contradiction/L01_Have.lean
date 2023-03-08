import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import TestGame.ToBePorted

Game "TestGame"
World "Contradiction"
Level 1

Title "Have"

Introduction
"
Manchmal, wollen wir nicht am aktuellen Goal arbeiten, sondern zuerst ein
Zwischenresultat beweisen, welches wir dann benützen können.

Mit `have [Name] : [Aussage]` kann man ein Zwischenresultat erstellen,
dass man anschliessen beweisen muss.

Wenn du zum Beispiel die Annahmen `(h : A → ¬ B)` und `(ha : A)` hast, kannst
du mit
```
have g : ¬ B
apply h
assumption
```
eine neue Annahme `(g : ¬ B)` erstellen. Danach beweist du zuerst diese Annahme,
bevor du dann mit dem Beweis forfährst.
"

Statement
    "Angenommen, man hat eine Implikation $A \\Rightarrow \\neg B$ und weiss, dass
    $A \\land B$ wahr ist. Zeige, dass dies zu einem Widerspruch führt."
    (A B : Prop) (h : A → ¬ B) (k : A ∧ B) : False := by
  rcases k with ⟨h₁, h₂⟩
  have h₃ : ¬ B
  apply h
  assumption
  contradiction

Hint (A : Prop) (B : Prop) (h : A → ¬ B) (k : A ∧ B) : False =>
" Fang mal damit an, das UND in den Annahmen mit `rcases` aufzuteilen.
"

Hint (A : Prop) (B : Prop) (h : A → ¬ B) (k : A) (f : B) : False =>
"
Auf Deutsch: \"Als Zwischenresultat haben wir `¬ B`.\"

In Lean :

```
have k : ¬ B
[Beweis von k]
```
"

-- example (n : ℕ) : n.succ + 2 = n + 3 := by
-- ring_nf

Conclusion ""

NewTactic «have»
DisabledTactic «suffices»

NewDefinition Even Odd
NewLemma not_even not_odd
