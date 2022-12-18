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
"Aber, die Aussagen müssen wirklich exakte Gegenteile sein.

Hier musst du zuerst eines der Lemmas `(not_odd : ¬ odd n ↔ even n)` oder
`(not_even : ¬ even n ↔ odd n)` benützen, um einer der Terme umzuschreiben."

Statement
    "Sei $n$ eine natürliche Zahl die sowohl gerade wie auch ungerade ist.
    Zeige, dass daraus $n = 42$ folgt. (oder, tatsächlich $n = x$ für jedes beliebige $x$)."
    (n : ℕ) (h_even : even n) (h_odd : odd n) : n = 42 := by
  rw [← not_even] at h_odd
  contradiction

Message (n : ℕ) (h_even : even n) (h_odd : odd n) : n = 42 =>
"Schreibe zuerst eine der Aussagen mit `rw [←not_even] at h_odd` um, damit diese genaue
Gegenteile werden."

Conclusion ""

Tactics contradiction rw

Lemmas even odd not_even not_odd
