import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import TestGame.ToBePorted

Game "TestGame"
World "Contradiction"
Level 3

Title "Ad absurdum"

Introduction
"
Aber, die Aussagen müssen wirklich exakte Gegenteile sein.

Hier musst du zuerst eines der Lemmas `not_odd : ¬ odd n ↔ even n` oder
`not_even : ¬ even n ↔ odd n` benützen, um einer der Terme umzuschreiben.
"

Statement
    "Ein Widerspruch impliziert alles."
    (n : ℕ) (h₁ : even n) (h₂ : odd n) : n = 128 := by
  rw [← not_even] at h₂
  contradiction

Message (n : ℕ) (h₁ : even n) (h₂ : odd n) : n = 128 =>
"Schreibe zuerst eine der Aussagen mit `rw [←not_even] at h₂` um, damit diese genaue
Gegenteile sind."

Conclusion
"
Detail: `¬ A` ist übrigens als `A → false` implementiert, was aussagt, dass
\"falls `A` wahr ist, impliziert das `false` und damit einen Widerspruch\".
"
-- TODO: Oder doch ganz entfernen?

Tactics contradiction
