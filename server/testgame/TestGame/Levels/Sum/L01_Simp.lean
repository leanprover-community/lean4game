import TestGame.Metadata

import TestGame.Options.BigOperators

set_option tactic.hygienic false

Game "TestGame"
World "Sum"
Level 1

Title "Simp"

Introduction
"
In diesem Kapitel lernen wir endliche Summen und mehr Übungen zur Induktion.

Eine endliche Summe läuft erstmal immer über einen endlichen Index
`Fin n`, welcher $n$ Elemente
$\\{0, 1, \\ldots, n-1\\}$ beinhaltet.

Der Syntax für  $\\sum_{i=0}^n a_i$ ist `∑ i : Fin n, _` (\\sum)

Als erstes kann die Taktik `simp` (für \"simplification\") ganz viel Triviales vereinfachen.
`simp` ist eine der stärksten Taktiken in Lean und verwendet
ganz viele markierte Lemmas um das Goal zu vereinfachen.

Zum Beispiel kennt es ein Lemma das ungefähr so aussieht:

```
@[simp]
lemma sum_const_add (n : ℕ) : (∑ i in Fin n, 0) = 0 := by
  sorry
```

Die Taktik `simp` benützt alle Lemmas, die mit `@[simp]` markiert sind.

(Tipp: `simp?` zeigt an, welche Lemmas `simp` benutzen würde.)
"

open BigOperators

Statement
"Zeige $\\sum_{i = 0} ^ {n-1} (0 + 0) = 0$."
    (n : ℕ) : (∑ i : Fin n, (0 + 0)) = 0 := by
  simp

NewTactics simp
