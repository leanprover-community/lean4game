import Adam.Metadata
import Mathlib.Tactic.Ring

Game "Adam"
World "Predicate"
Level 4

Title "Natürliche Zahlen"

Introduction
"
*Evenines* Berater meldet sich.

**Berater**: Das stimmt wohl, aber das Problem, das uns eigentlich beschäftigt hat, eure
Natürlichkeit, war folgendes:
"

Statement
    (x y z : ℕ) (h : x = 2 * y + 1) (g : z  = 3 * y + 1): x ^ 2 = 4 * y ^ 2 + z + y := by
  Hint "**Du**: Ich versteh das Pattern. Wenn ich zuerst alles so umschreibe, dass
  das Goal nur noch rechnen und umsortieren ist, dann kann `ring` den Rest machen!

  **Robo**: Noch ein Trick: Entweder kannst du zwei Befehle `rw [h₁]` und `rw [h₂]` schreiben,
  oder du kannst das gleich in einem machen : rw [h₁, h₂]."
  rw [h, g]
  ring


Conclusion
"
*Evenine* bedankt sich nochmals für die Botschaft und ihr werdet zu einem kleineren Busch geführt,
der ein gemütlich warmes Innenleben an den Tag legt.
"

NewTactic ring rw
