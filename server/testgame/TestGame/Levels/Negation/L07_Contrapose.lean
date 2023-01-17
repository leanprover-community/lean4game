import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import TestGame.ToBePorted

Game "TestGame"
World "Proving"
Level 3

Title "Kontraposition"

Introduction
"
Im Gegensatz dazu kann man auch einen Beweis durch Kontraposition führen.
Das ist kein Widerspruch, sondern benützt dass `A → B` und `(¬ B) → (¬ A)`
logisch equivalent sind.

Wenn das Goal eine Implikation ist, kann man `contrapose` anwenden.
"

Statement
    "Ist n² ungerade, so ist auch n ungerade. Beweise durch Kontraposition."
    (n : ℕ) : odd (n ^ 2) → odd n := by
  contrapose
  rw [not_odd]
  rw [not_odd]
  apply even_square

Message (n : ℕ) (h : odd (n ^ 2)) : odd n =>
"`intro` wär generell ein guter Ansatz! Aber hier wollen wir `contrapose` benützen, was eine
Implikation benötigt, deshalb ist `intro` hier der falsche Weg!"


Message (n : ℕ) : odd (n ^ 2) → odd n =>
"Mit `contrapose` kann man die Implikation zu
`¬ (even n) → ¬ (even n^2)` umkehren."

Hint (n : ℕ) : ¬odd n → ¬odd (n ^ 2) => "Du kennst bereits ein Lemma um `¬ odd ...` mit `rw`
umzuschreiben"

Message (n : ℕ) : even n → ¬odd (n ^ 2) => "rw [not_odd] muss hier zweimal angewendet werden,
da rw das erste Mal `not_odd n` gebraucht hat und das zweite Mal `not_odd (n^2)` benützt."

Message (n : ℕ) : even n → even (n ^ 2) => "Diese Aussage hast du bereits als Lemma bewiesen."

Tactics contrapose rw apply
Lemmas even odd not_even not_odd even_square
