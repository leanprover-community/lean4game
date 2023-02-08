import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring
import Mathlib

import TestGame.ToBePorted

Game "TestGame"
World "Contradiction"
Level 3

Title "Per Widerspruch"

Introduction
"
Eine sehr nützliche Beweismethode ist per Widerspruch.

Wir habe schon gesehen, dass `contradiction` einen Widerspruch in den Annahmen
sucht, und damit jegliches beweisen kann.

Um dorthin zu kommen, können wir `by_contra h` brauchen, welches das aktuelle
Goal auf `False` setzt und die Negierung des Goals als Annahme hinzufügt.

Insbesondere braucht man `by_contra h` meistens, wenn im Goal eine Negierung
steht:
"

Statement
"Angenommen $B$ ist falsch und es gilt $A \\Rightarrow B$. Zeige, dass $A$ falsch sein
muss."
    (A B : Prop) (g : A → B) (b : ¬ B) : ¬ A := by
  by_contra a
  suffices b : B
  contradiction
  apply g
  assumption


HiddenHint (A : Prop) (B : Prop) (h : A → B) (b : ¬ B) : ¬ A =>
"`by_contra h` nimmt das Gegenteil des Goal als Annahme `(h : A)` und setzt das
Goal auf `False`."

Hint (A : Prop) (B : Prop) (h : A → B) (b : ¬ B) (a : A) : False =>
"Jetzt kannst du mit `suffices` oder `have` Fortschritt machen."

HiddenHint (A : Prop) (B : Prop) (h : A → B) (b : ¬ B) (a : A) : False =>
"Zum Beispiel `suffices hb : B`."


Conclusion ""

NewTactics by_contra sufficesₓ haveₓ contradiction apply assumption
