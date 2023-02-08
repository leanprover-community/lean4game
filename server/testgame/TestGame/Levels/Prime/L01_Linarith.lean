import TestGame.Metadata
import Mathlib.Tactic.Linarith

import TestGame.ToBePorted

Game "TestGame"
World "Prime"
Level 1

Title "Kleinergleich"

Introduction
"
Ungleichheiten werden in Lean generell immer als Kleinergleich `≤` (`\\le`) oder `<`
geschrieben.

Die Symbole `≥` und `>` gibt es zwar auch, sind aber nur Notation für die gleiche
Aussage mit `≤` und `<`.

Die Taktik `linarith` kann alle Systeme von linearen (Un-)gleichungen über `ℤ`, `ℚ`, etc. lösen.
Über `ℕ` ist sie etwas schwächer, aber einfache Aussagen kann sie trotzdem beweisen.
"

Statement
"Wenn $n \\ge 2$, zeige, dass $n$ nich Null sein kann."
    (n : ℕ) (h : 2 ≤ n) : n ≠ 0 := by
  linarith

NewTactics linarith
