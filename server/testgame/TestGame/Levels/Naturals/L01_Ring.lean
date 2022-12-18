import TestGame.Metadata
import Mathlib.Tactic.Ring

--set_option tactic.hygienic false

Game "TestGame"
World "Nat"
Level 1

Title "Natürliche Zahlen"

Introduction
"
Wir sind den narürlichen Zahlen `ℕ` (`\\N`) schon begegnet. Dabei haben wir
gesehen, dass explizite Gleichungen wie `2 + 3 * 5 = 17` implementationsbedingt
bereits mit `rfl` bewiesen werden können.

Algemeinere Gleichungen mit Variablen kann man mit der Taktik `ring` lösen.
"

Statement
    "Zeige $(x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2$."
    (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

Message (x : ℕ) (y : ℕ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 =>
"`ring` übernimmt den ganzen Spaß."

Conclusion
"
Die Taktik heisst übrigens `ring` weil sie dafür entwickelt wurde, Gleichungen in einem abstrakten
Ring zu lösen, funktioniert aber auch auf `ℕ`, auch wenn dieses kein Ring ist
(erst `ℤ` ist ein Ring).
"

Tactics ring
