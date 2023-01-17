import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

import TestGame.ToBePorted

Game "TestGame"
World "Proposition"
Level 8

Title "Widerspruch"

Introduction
"
Drittens kann die Taktik `contradiction` auch einen Widerspruch finden,
wenn zwei Annahmen genaue Gegenteile voneinander sind.
Also z.B. `(h : A)` und `(g : ¬ A)`.

Da `≠` als `¬(· = ·)` gelesen wird, gilt dasselbe für Annahmen `(h : a = b)` und `(g : a ≠ b)`.
"

Statement absurd
    "Sei $n$ eine natürliche Zahl die sowohl gleich als auch ungleich `10` ist.
    Zeige, dass daraus $n = 42$ folgt. (oder, tatsächlich $n = x$ für jedes beliebige $x$)"
    (n : ℕ) (h : n = 10) (g : (n ≠ 10)) : n = 42 := by
  contradiction

Conclusion
"
"

Tactics contradiction
