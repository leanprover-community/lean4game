import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import TestGame.ToBePorted

Game "TestGame"
World "Proving"
Level 2

Title "Widerspruch"

Introduction
"
Zwei wichtige Beweisformen sind per Widerspruch und per Kontraposition. Hier
schauen wir beide an und auch den Unterschied.

Um einen Beweis per Widerspruch zu führen, kann man mit `by_contra h` annehmen,
dass das Gegenteil des Goals wahr sei, und dann einen Widerspruch erzeugen.

**Bemerkung:** Besonders beim Beweis durch Widerspruch ist es hilfreich, wenn man
Zwischenresultate erstellen kann.
`suffices h₁ : ¬(Odd (n ^ 2))` erstellt zwei neue Goals:

1) Ein Beweis, wieso es genügt `¬(Odd (n ^ 2))` zu zeigen (\"weil das einen Widerspruch zu
`h` bewirkt\").
2) Einen Beweis des Zwischenresultats `suffices h₁ : ¬(Odd (n ^ 2))`

Alternativ macht `have h₁ : ¬(Odd (n ^ 2))` genau das gleiche, vertauscht aber die
Beweise (1) und (2), so dass man zuerst `h₁` beweist, und dann den eigentlichen Beweis
fortsetzt.
"

Statement
    "Ist n² ungerade, so ist auch n ungerade. Beweise durch Widerspruch."
    (n : ℕ) (h : Odd (n ^ 2)) : Odd n := by
  by_contra g
  suffices d : ¬ Odd (n ^ 2) -- TODO: I don't like this
  contradiction

  rw [not_odd] at g
  rw [not_odd]
  apply even_square
  assumption

Message (n : ℕ) (h : Odd (n^2)) : Odd n =>
"Schreibe `by_contra h₁` um einen Beweis durch Widerspruch zu starten."

Message (n : ℕ) (g : ¬ Odd n) (h : Odd (n^2)) : False =>
"Nun *genügt es zu zeigen, dass* `¬Odd (n ^ 2)` wahr ist,
denn dann erhalten wir einen Widerspruch zu `h`.

Benütze dafür `suffices h₂ : ¬Odd (n ^ 2)`.
"

Message (n : ℕ) (g : ¬ Odd (n^2)) (h : Odd (n^2)) : False =>
"Hier musst du rechtfertigen, wieso das genügt. In unserem Fall, weil
dadurch einen Widerspruch entsteht."

Hint (n : ℕ) (g : ¬ Odd (n^2)) (h : Odd (n^2)) : False =>
"Also `contradiction`..."

Message (n : ℕ) (g : ¬ Odd n) (h : Odd (n^2)) : ¬ Odd (n^2) =>
"Das Zwischenresultat `¬Odd (n^2)` muss auch bewiesen werden.
Hier ist wieder das Lemma `not_Odd` hilfreich."

Hint (n : ℕ) (g : ¬ Odd n) (h : Odd (n^2)) : Even (n^2) =>
"Mit `rw [not_Odd] at *` kannst du im Goal und allen Annahmen gleichzeitig umschreiben."

Message (n: ℕ) (h : Odd (n ^ 2)) (g : Even n) : Even (n ^ 2) =>
"Diese Aussage hast du bereits als Lemma bewiesen."

Hint (n: ℕ) (h : Odd (n ^ 2)) (g : Even n) : Even (n ^ 2) =>
"Probiers mit `apply ...`"


Tactics contradiction by_contra rw apply assumption -- TODO: suffices, have

Lemmas Odd Even not_odd not_even even_square
