import TestGame.Metadata
import Mathlib.Tactic.Ring

--set_option tactic.hygienic false

Game "TestGame"
World "Predicate"
Level 1

Title "Natürliche Zahlen"

Introduction
"
**Evenine**: Willkommen Reisende! Wir leben hier in Einklang mit der Natur und allem natürlichen,
so sagt mir, könnt ihr mit natürlichen Zahlen umgehen?
"

Statement (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  Hint "**Du**: Das hab ich in der Schule gelernt, man rechnet das einfach aus,
  indem man die Terme umsortiert.

  **Robo**: Behaupte doch mit `ring`, dass das so ist.

  **Du**: Aber `ℕ` ist doch gar kein Ring?

  **Robo**: `ring` funktioniert schon für Halbringe, aber sie heisst ring, weil sie auf
  (kommutativen) Ringen am besten funktioniert.
  "
  ring

Conclusion
"
*Evenine: Ja das stimmt schon. Und das genügt uns auf diesem Planet auch als Antwort.*
"

NewTactic ring
