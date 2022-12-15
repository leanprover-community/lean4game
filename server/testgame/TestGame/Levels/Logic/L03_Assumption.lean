import TestGame.Metadata

Game "TestGame"
World "Logic"
Level 3

Title "Annahmen"

Introduction
"
Um Aussagen zu formulieren brauchen wir Annahmen. Das sind zum einen Objekte, wie \"sei `n` eine
natürliche Zahl\", und Annahmen über diese Objekte, von denen wir wissen, dass sie wahr sind.
Zum Beispiel
\"und angenommen, dass `n` strikt grösser als `1` ist\".

In Lean schreibt man beides mit dem gleichen Syntax: `(n : ℕ) (h : 1 < n)` definiert
zuerst eine natürliche Zahl `n` und eine Annahme dass `1 < n` (die Annahme kriegt
den Namen `h`).

Wenn das Goal genau einer Annahme entspricht, kann man diese mit `assumption` beweisen.
"

Statement triviale_angelegenheit
    "Angenommen `1 < n`. dann ist `1 < n`."
    (n : ℕ) (h : 1 < n) : 1 < n := by
  assumption

Message (n : ℕ) (h : 1 < n) : 1 < n =>
  "`assumption` sucht nach einer Annahme, die dem Goal entspricht."

Conclusion ""

Tactics assumption
