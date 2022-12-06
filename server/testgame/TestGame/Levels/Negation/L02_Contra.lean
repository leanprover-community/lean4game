import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

Game "TestGame"
World "Contradiction"
Level 2

Title "Widerspruch"

Introduction
"
Ähnlich siehts aus, wenn man Annahmen hat, die direkte Negierung voneinander sind,
also `(h : A)` und `(g : ¬ A)`. (`\\not`)
"

Statement
  "Ein Widerspruch impliziert alles."
    (A : Prop) (n : ℕ) (h : ∃ x, 2 * x = n) (g : ¬ (∃ x, 2 * x = n)) : A := by
  contradiction

Conclusion
"
Detail: `¬ A` ist übrigens als `A → false` implementiert, was aussagt, dass
\"falls `A` wahr ist, impliziert das `false` und damit einen Widerspruch\".
"
-- TODO: Oder doch ganz entfernen?

Tactics contradiction
