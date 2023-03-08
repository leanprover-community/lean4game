import TestGame.Metadata
import Std.Tactic.RCases

set_option tactic.hygienic false

Game "TestGame"
World "Proposition"
Level 10

Title "Und"

Introduction
"
Der nächste Formalosoph in der Reihe hat seine Frage bereìts mitgebracht.
Er legt sie uns vor, setzt sich hin, und häkelt.
"
Statement "" (A B : Prop) (hA : A) (hB : B) : A ∧ B := by
  constructor
  assumption
  assumption

Hint (A B : Prop) (hA : A) (hB : B) : A ∧ B =>
"
**Du**:  Also, wir haben zwei Annahmen: `{A}` gilt, und `{B}` gilt. Auch. Und beweisen sollen wir
dass `{A} und {B}` gilt.  Ich glaube, diese Formalospinner treiben mich noch zur Verzweiflung.
Kann ich nicht wieder `trivial` sagen?

**Robo** Nee, diesmal wird das nicht funktionieren.
Du musst das Beweisziel einfach in zwei Teile zerlegen. Probier mal `constructor`.

**Du** Du meinst, `destructor`??

**Robo** Nein, `constructor`. Ich weiß das ist verwirrend,
aber die nennen das hier so weil man die Aussage aus mehreren Teilen
konstruieren kann.
"

HiddenHint (A : Prop) (hA : A) : A =>
"
**Robo**   Schau mal, das ist Zauberpapier.
Jetzt haben wir auf einmal zwei Beweisziele.
Hier ist dast Ziel `{A}`.
Ich glaube, Du weißt schon, wie man die jeweils erreicht.
Die Ziele stehen ja jeweils in den *Annahmen*.
"

Conclusion
"
**Robo** Super!

Ihm scheinen diese Fragen inzwischen Spaß zu machen.

**Robo** Meinst Du, dieser Hebel, an dem \"Editor mode\" steht, ist echt?
Oder ist der nur gemalt?  Probier mal!
"

NewTactic constructor
DisabledTactic tauto
