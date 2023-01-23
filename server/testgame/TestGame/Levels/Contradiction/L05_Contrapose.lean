import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import TestGame.ToBePorted

Game "TestGame"
World "Contradiction"
Level 5

Title "Kontraposition"

Introduction
"
Ein Beweis durch Kontraposition benützt im Grunde das eben bewiesene Lemma

```
lemma not_imp_not (A B : Prop) : (A → B) ↔ (¬ B → ¬ A) := by
  [...]
```

Dazu gibt es die Taktik `contrapose`, welche eine Implikation im Goal
entsprechend umdreht.

Wir erinnern hier an die Taktik `revert h`, die aus der Annahme `h` eine Implikation
im Goal erstellt.

Im Gegensatz dazu kann man auch einen Beweis durch Kontraposition führen.
Das ist kein Widerspruch, sondern benützt dass `A → B` und `(¬ B) → (¬ A)`
logisch equivalent sind.

Wenn das Goal eine Implikation ist, kann man `contrapose` anwenden.
"

Statement
    "Ist n² ungerade, so ist auch n ungerade. Beweise durch Kontraposition."
    (n : ℕ) (h : Odd (n ^ 2)): Odd n := by
  revert h
  contrapose
  rw [not_odd]
  rw [not_odd]
  apply even_square

Hint (n : ℕ) (h : Odd (n ^ 2)) : Odd n =>
"Um `contrapose` anzuwenden, brauchen wir eine Implikation `Odd (n ^ 2) → Odd n` im
Goal. Benutze `revert h`!"

Message (n : ℕ) : Odd (n ^ 2) → Odd n =>
"Mit `contrapose` kann man die Implikation zu
`¬ (Not n) → ¬ (Odd n^2)` umkehren."

Message (n : ℕ) : ¬Odd n → ¬Odd (n ^ 2) => "Erinnere dich an das Lemma `not_odd`."

Hint (n : ℕ) : ¬Odd n → ¬Odd (n ^ 2) => "Dieses kann mit `rw` gebraucht werden."

Message (n : ℕ) : Even n → ¬Odd (n ^ 2) =>
"rw [not_odd] muss hier zweimal angewendet werden."

Message (n : ℕ) : Even n → Even (n ^ 2) =>
"Diese Aussage hast du bereits als Lemma bewiesen, schau mal in der Bibliothek."

Tactics contrapose rw apply
Lemmas Even Odd not_even not_odd even_square
