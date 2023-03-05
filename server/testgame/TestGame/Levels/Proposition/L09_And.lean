import TestGame.Metadata
import Std.Tactic.RCases

set_option tactic.hygienic false

Game "TestGame"
World "Proposition"
Level 10

Title "Und"

Introduction
"
Der nächste Formalosoph in der Reihe hat seine Frage bereìts mitgebracht. Er legt sie uns vor, setzt sich hin, und häkelt.
"
Statement "" (A B : Prop) (hA : A) (hB : B) : A ∧ B := by
  constructor
  assumption
  assumption

Hint
"
**Du**:  Also, wir haben zwei Annahmen: `A` gilt, und `B` gilt.  Auch.  Und beweisen sollen wir … `A und B` gilt.  Ich glaube, diese Formalospinner treiben mich noch zur Verzweiflung.  Kann ich nicht wieder `trivial` sagen?

**Robo** Nee, diesmal wird das nicht funktionieren.  Du musst das Beweisziel einfach in zwei Teile zerlegen. Probier mal `constructor`.

**Du** Du meinst, `destructor`??

**Robo** Nein, `constructor`.  Ist verwirrend, ich weiß, aber so nennen die das hier.
"

HiddenHint (A : Prop) (hA : A) : A =>
"
**Robo**   Schau mal, das ist Zauberpapier.  Jetzt haben wir auf einmal zwei Beweisziele: `A` und `B`.  Ich glaube, Du weißt schon, wie man die jeweils erreicht.  Die Ziele stehen ja jeweils in den *Annahmen*.
"

Conclusion 
"
**Robo** Super!

Ihm scheinen diese Fragen inzwischen Spaß zu machen.

**Robo** Meinst Du, dieser Hebel, an dem \"Editor mode\" steht, ist echt?  Oder ist der nur gemalt?  Probier mal!
"

NewTactics constructor
DisabledTactics tauto
