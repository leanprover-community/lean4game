import Mathlib.Algebra.BigOperators.Basic
import Mathlib

import TestGame.Metadata

set_option tactic.hygienic false

Game "TestGame"
World "Induction"
Level 1

Title "Simp"

Introduction
"
In diesem Kapitel lernen wir endliche Summen und Induktion kennen.

Eine endliche Summe läuft erstmal immer über einen endlichen Index
`Fin n`, welcher $n$ Elemente
$\\{0, 1, \\ldots, n-1\\}$ beinhaltet.

Der Syntax für`∑ i : Fin n, (...)` (\\sum) ist der Syntax für $\\sum_{i=0}^n …$

Als kann die Taktik `simp` (für \"simplification\") ganz viel Triviales vereinfachen.
`simp` ist eine der stärksten Taktiken in Lean und verwendet
ganz viele markierte Lemmas um das Goal zu vereinfachen.

Zum Beispiel kennt es ein Lemma das ungefähr so aussieht:

```
@[simp]
lemma sum_const_add (n : ℕ) : (∑ i in Fin n, 0) = 0 := by
  [...]
```

Mit `simp?` anstatt `simp` kannst du zudem schauen, welche Lemmas von `simp` benutzt wurde.
"

Statement
"Zeige dass `∑_{i = 0} ^ {n-1} 0 = 0 + 0`."
    (n : ℕ) : (∑ i : Fin n, 0) = 0 + 0 := by
  simp

Tactics simp
