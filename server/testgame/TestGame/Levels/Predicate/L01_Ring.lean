import TestGame.Metadata
import Mathlib.Tactic.Ring

--set_option tactic.hygienic false

Game "TestGame"
World "Predicate"
Level 1

Title "Natürliche Zahlen"

Introduction
"
Wir sind den narürlichen Zahlen `ℕ` (`\\N`) schon kurz begegnet.

Gleichungen, die nur die Operationen `+, -, *, ^` (Addition, Subtraktion, Multiplikation, Potenz)
und Variablen enthalten, kann Lean mit der Taktik `ring` beweisen.

Diese Taktik funktioniert nicht nur über den natürlichen Zahlen,
sondern auch in (kommutativen) Gruppen, Ringen, und Körpern. Sie heisst `ring`, weil sie für Ringe
entwickelt wurde.

(Note: Division `/` ignorieren wir hier erst einmal, weil diese auf `ℕ`
nicht kanonisch definiert ist.)
"

Statement
    "Zeige $(x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2$."
    (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

Hint (x : ℕ) (y : ℕ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 =>
"`ring` übernimmt den ganzen Spaß."

Conclusion
"
Die Taktik heisst übrigens `ring` weil sie dafür entwickelt wurde, Gleichungen in einem abstrakten
Ring zu lösen, funktioniert aber auch auf `ℕ`, auch wenn dieses kein Ring ist
(erst `ℤ` ist ein Ring).
"

Tactics ring

#eval 4 / 6
