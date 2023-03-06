import TestGame.Metadata
import Mathlib.Tactic.Tauto

Game "TestGame"
World "Proposition"
Level 1

Title "Automatisierung"

Introduction
"
Gerade seid Ihr auf Königin *Logisindes* Planeten. Sie kommt ohne Umschweife zum Punkt:

**Logisinde**  Werte Wesen aus fremden Welten, gestatten Sie eine Frage. Warum gilt …

Und er kritzelt etwas auf ein Stück Papier:  oben ein paar Annahmen, unten eine Schlussfolgerung.
Dazwischen sollst Du offenbar einen Beweis eintragen.
Du siehst Robo hilflos an.
"

Statement ""
    (A B C : Prop) :
    ¬((¬B ∨ ¬ C) ∨ (A → B)) → (¬A ∨ B) ∧ ¬ (B ∧ C) := by
  tauto

Hint  (A B C : Prop) :
    ¬((¬B ∨ ¬ C) ∨ (A → B)) → (¬A ∨ B) ∧ ¬ (B ∧ C) =>
 "**Robo**  Das ist ganz einfach.  Mit `{A} {B} {C} : Prop` meint er:
 `{A}`, `{B}` und `{C}` sind irgendwelche Aussagen (*propositions*).
 Und mit `→` meint sie ⇒, also “impliziert”. Die anderen Symbole kennst Du, oder?

**Du** Ehhm, ja.  Aber da muss ich jetzt trotzdem erst einmal überlegen.

**Robo** (flüsternd) Behaupte doch einfach, dass sei eine Tautologie.

**Du** Ernsthaft?

**Robo** Ja.  Schreib einfach `tauto`.

**Robo** Mach schon …
"

Conclusion
"
**Logisinde** (etwas konsterniert)  Ja, das ist streng genommen richtig.
Aber glaubt bloß nicht, dass Ihr damit auf *diesem* Planeten viel weiterkommt!
Meine Untertanen verstehen `tauto` nicht.  Da müsst Ihr Euch schon etwas mehr anstrengen.
"

NewTactics tauto
