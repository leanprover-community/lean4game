import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

import TestGame.ToBePorted

Game "TestGame"
World "Contradiction"
Level 2

Title "Ad absurdum"

Introduction
"
Ähnlich siehts aus, wenn man Annahmen hat, die direkte Negierung voneinander sind,
also `(h : A)` und `(g : ¬ A)`. (`\\not`)
"

Statement absurd
    "Sei $n$ eine natürliche Zahl die sowohl gerade wie auch nicht gerade ist.
    Zeige, dass daraus $n = 42$ folgt. (oder, tatsächlich $n = x$ für jedes beliebige $x$)"
    (n : ℕ) (h : even n) (g : ¬ (even n)) : n = 42 := by
  contradiction

Conclusion
"
"

Tactics contradiction
