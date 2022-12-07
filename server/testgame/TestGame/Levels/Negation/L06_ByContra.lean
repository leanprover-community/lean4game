import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import TestGame.ToBePorted

Game "TestGame"
World "Contradiction"
Level 6

Title "Widerspruch"

Introduction
"
Um einen Beweis per Widerspruch zu führen, kann man mit `by_contra h` annehmen,
dass das Gegenteil des Goals wahr sei, und dann einen Widerspruch erzeugen.
"

Statement
  "Ist n² ungerade, so ist auch n ungerade. Beweise durch Widerspruch."
    (n : ℕ) (h : odd (n ^ 2)) : odd n := by
  by_contra g
  rw [not_odd] at g

  suffices ¬ odd (n ^ 2) by contradiction -- TODO: I don't like this

  rw [not_odd]
  apply even_square
  assumption

Message : false =>
"Es gibt mehrere Möglichkeiten, wie man nach einem `by_contra` weitergeht.

Hier wollen wir einen Widerspruch zu `h` machen. Wir machen das mit
`suffices ¬ odd (n ^ 2) by contradiction`, worauf man dann nur noch `¬ odd (n ^ 2)`
zeigen muss."

Hint (n : ℕ) : ¬ (odd (n ^ 2)) =>
"Das Lemma `not_odd` ist hilfreich."

Message (n: ℕ) (h : odd (n ^ 2)) (g : even n) : even (n ^ 2) =>
"Das haben wir schon gezeigt. Mit `apply even_square` kannst du das Lemma anwenden."

Tactics contradiction by_contra rw apply assumption -- TODO: suffices

Lemmas odd even not_odd not_even even_square
