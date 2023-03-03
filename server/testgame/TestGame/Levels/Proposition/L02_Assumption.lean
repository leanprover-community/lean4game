import TestGame.Metadata

Game "TestGame"
World "Proposition"
Level 3

Title "Annahmen"

Introduction
"
Um spannendere Aussagen zu formulieren brauchen wir Objekte und Annahmen über diese
Objekte.

Hier zum Beispiel haben wir eine natürliche Zahl $n$ und eine Annahme $1 < n$, die
wir $h$ nennen.

Wenn das Goal genau einer Annahme entspricht, kann man diese mit `assumption` beweisen.


**Note:**
Wenn du den \"Editor mode\" umstellst, kannst du sehen, wie die Aufgabe in vollständigem
Lean-Code geschrieben wird. Hier sieht das wie folgt aus:

```
example (n : ℕ) (h : 1 < n) : 1 < n := by
  sorry
```

Also

```
example [Objekte/Annahmen] : [Aussage] := by
  [Beweis]
```
"

Statement
"Angenommen $1 < n$. Dann ist $1 < n$."
    (n : ℕ) (h : 1 < n) : 1 < n := by
  assumption

HiddenHint (n : ℕ) (h : 1 < n) : 1 < n =>
  "`assumption` sucht nach einer Annahme, die dem Goal entspricht."


Conclusion ""

NewTactics assumption
DisabledTactics tauto
