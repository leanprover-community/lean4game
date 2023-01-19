import TestGame.Metadata
import Mathlib.Tactic.Ring

Game "TestGame"
World "Predicate"
Level 4

Title "Natürliche Zahlen"

Introduction
"
Oft braucht man eine Kombination von `rw` und `ring` um Gleichungen zu lösen.

Zuerst setzt man mit `rw` die vorhandenen Annahmen ein, und sobald die beiden Seiten
einer Gleichung im Goal rechnerisch gleich sind, kan `ring` dies beweisen.
"

Statement
    "Angenommen, man hat die Gleichung $x = 2 * y + 1$, zeige
    $x ^ 2 = 4 * y ^ 2 + 3 * y + 1 + y$.  "
    (x y : ℕ) (h : x = 2 * y + 1) : x ^ 2 = 4 * y ^ 2 + 3 * y + 1 + y := by
  rw [h]
  ring

Message (x : ℕ) (y : ℕ) (h : x = 2 * y + 1) : x ^ 2 = 4 * y ^ 2 + 3 * y + 1 + y =>
  "Die Annahme `h` kannst du mit `rw [h]` benützen."

Message (y : ℕ) : (2 * y + 1) ^ 2 = 4 * y ^ 2 + 3 * y + 1 + y =>
  "Jetzt kann `ring` übernehmen."

Conclusion ""

Tactics ring rw
