import Adam.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Cases
import Mathlib

Game "Adam"
World "Implication"
Level 11

Title "by_cases"

Introduction
"
**Du**: Sag mal, hätten wir nicht auch einfach zwei Fälle anschauen können? 
Wenn `A` wahr ist, beweisen wir die rechte Seite, sonst die Linke.

**Robo**: Tatsächlich, `by_cases h : A` würde genau das machen!

**Du** (zum Operationsleiter): Können wir das Blatt bitte noch einmal haben?
"

Statement (A : Prop) : ¬A ∨ A := by
  Hint (hidden := true) "**Du**: Wie noch einmal?

  **Robo**: Also `by_cases h : A` erstellt zwei Goals. Im ersten hast Du `(h : A)` zur
  Verfügung, im zweiten `(h : ¬ A)`."
  by_cases h : A
  right
  assumption
  left
  assumption

Conclusion
"
**Du**: So gefällt mir der Beweis viel besser!
"

NewTactic by_cases
DisabledTactic tauto
