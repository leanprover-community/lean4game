import TestGame.Metadata
import Mathlib.Data.Nat.Basic -- TODO

Game "TestGame"
World "Proposition"
Level 4

Title "Logische Aussagen"

Introduction
"
Ein dritter Untertan kommt mit folgendem Problem.
"

Statement "
**Robo** Hier bedeutet `A : Prop` wieder, dass `A` irgendeine Aussage ist.
   Und `hA` ist eine Name für die Annahme, dass `A` wahr ist.

**Du** Und unter dieser Annahme sollen wir jetzt `A` beweisen?

**Robo** Ja.  Da kommst Du jetzt selbst drauf, wie das geht, oder?
"
  (A : Prop) (hA : A) : A := by
  assumption


HiddenHint (A : Prop) (hA : A) : A =>
"Ist doch genau wie eben:  die Aussage, die zu beweisen ist, gehört selbst zu den Annahmen. Also wird `asumption` auch wieder funktionieren."

Conclusion
"
**Untertan** Das ging ja schnell.  Super!  Vielen Dank.
"

NewTactics assumption
DisabledTactics tauto
