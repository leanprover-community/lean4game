import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import TestGame.ToBePorted

Game "TestGame"
World "Proving"
Level 1

Title "Ad absurdum"

Introduction
"
In diesem Kapitel lernen wir die wichtigsten Beweistechniken kennen.

Zuerst repetieren wir, dass man vorhandene Lemmas mit `rw` und `apply` benützen kann.


  Aber, die Aussagen müssen wirklich exakte Gegenteile sein.

Hier musst du zuerst eines der folgenden Lemmas benützen, um einer der Terme umzuschreiben.

```
lemma not_odd (n : ℕ): ¬ odd n ↔ even n := by
  ...

lemma not_even (n : ℕ): ¬ even n ↔ odd n := by
  ...
```
"

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
