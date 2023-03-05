import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

--set_option tactic.hygienic false

Game "TestGame"
World "Proposition"
Level 12

Title "Oder"

Introduction
"
Der nächste bitte …
"

Statement
"Angenommen $A$ ist wahr, zeige $A \\lor (\\neg B))$."
    (A B : Prop) (hA : A) : A ∨ (¬ B) := by
  left
  assumption

Hint
" 
**Du** Muss ich jetzt wieder das Beweisziel de-konstruieren? 

**Robo** Nein, viel einfacher.  Wenn Du eine Oder-Aussage beweisen sollst, musst Du Dich einfach entscheiden, ob Du die linke oder rechte Seite beweisen willst.

**Du** Und wie erkläre ich meinem Formalosophen, welche Seite ich gern beweisen würde?  Ich will natürlich `A` beweisen!  

**Robo** Mit `left` bzw. `right'. Ist doch logisch, oder?
"

Hint (A : Prop) (B : Prop) (hA : A) : ¬ B =>
"
**Robo** Wusst gar nicht, dass Du eine Links-Rechts-Schwäche hast.  Probier's nochmal.
"

Conclusion
"
Auch dieser Formalosoph zieht zufrieden von dannen.
"

NewTactics left right assumption
DisabledTactics tauto
