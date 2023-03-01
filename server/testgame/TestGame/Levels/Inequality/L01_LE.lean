import TestGame.Metadata

Game "TestGame"
World "Inequality"
Level 1

Title "Kleinergleich"

Introduction
"
Ungleichheiten werden in Lean generell immer als Kleinergleich `≤` (`\\le`) oder `<`
geschrieben.

Die Symbole `≥` und `>` gibt es zwar auch, sind aber nur Notation für die gleiche
Aussage mit `≤` und `<`.

Zudem sind `<` und `≤` auf `ℕ` so definiert, dass `0 < n` und `1 ≤ n` per Definition
äquivalent sind. Die folgende Aussage ist also mit `rfl` beweisbar.
"

Statement
"$0 < n$ und $1 ≤ n$ sind äquivalente Aussagen."
    (n m : ℕ) : m < n ↔ m.succ ≤ n := by
  rfl
