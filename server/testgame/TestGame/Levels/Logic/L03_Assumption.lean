import TestGame.Metadata

Game "TestGame"
World "Logic"
Level 3

Title "Annahmen"

Introduction
"
Mathematische Aussagen haben Annahmen. Das sind zum einen Objekte, wie \"sei `n` eine
natürliche Zahl\", oder auch wahre Aussagen über diese Objekte, wie zum Beispiel
\"und angenommen, dass `n` strikt grösser als `1` ist\".

In Lean schreibt man beides mit dem gleichen Syntax: `(n : ℕ) (h : 1 < n)` definiert
zuerst `n` als natürliche Zahl und kreeirt eien Annahme, dass `1 < n`. Dieser Annahme geben wir
den Namen `h`.

Wenn das Goal genau einer Annahme entspricht, kann man diese mit `assumption` beweisen.
"

Statement triviale_angelegenheit
    "Angenommen `1 < n`. dann ist `1 < n`."
    (n : ℕ) (h : 1 < n) : 1 < n := by
  assumption

Conclusion ""

Tactics assumption
