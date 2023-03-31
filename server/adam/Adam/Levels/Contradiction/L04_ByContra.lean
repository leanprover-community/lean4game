import Adam.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring
import Mathlib

import Adam.ToBePorted

Game "Adam"
World "Contradiction"
Level 4

Title "Kontraposition"

Introduction
"
**Benedictus**:  Ich habe noch eine schöne Frage zu ungeraden Quadraten für Euch.  Aber vorher beweist Ihr besser noch diese Äquivalenz hier.  Ich gaube, die hat sogar bei Euch einen Namen: *Kontrapositionsäquivalenz*, oder so etwas.  Auf Leansch nennen wir die Äuqivalenz einfach `not_imp_not`.  Ist doch viel einleuchtender, oder?
"

Statement not_imp_not (A B : Prop) : A → B ↔ (¬ B → ¬ A) := by
  Hint "**Du**: Ja, das habe ich tatsächlich schon einmal gesehen.

  **Robo**:  Ja, klar hast du das schon einmal gesehen.  Das benutzen Mathematiker doch ständig.  Wenn ihnen zu $A ⇒ B$ nichts einfällt, zeigen sie stattdessen $¬B ⇒ ¬A$.  Ich würde das ja statt *Kontraposition* oder `not_imp_not` eher *von_hinten_durch_die_Brust_ins_Auge* nennen.  Aber gut, ich will mich nicht einmisschen.
  " 
  Hint (hidden := true) "**Robo**: Fang doch mal mit `constructor` an."
  constructor
  intro h b
  by_contra a
  Hint "**Robo**: Ich würde wieder mit `suffices g : B` einen Widerspruch herbeiführen."
  suffices b : B
  contradiction
  apply h
  assumption
  intro h a
  Hint "**Robo**: Hier würde ich ebenfalls einen Widerspruchsbeweis anfangen."
  by_contra b
  Hint (hidden := true) "**Robo**: `suffices g : ¬ A` sieht nach einer guten Option aus."
  suffices g : ¬ A
  contradiction
  apply h
  assumption

DisabledTactic rw
DisabledLemma not_not

Conclusion ""
