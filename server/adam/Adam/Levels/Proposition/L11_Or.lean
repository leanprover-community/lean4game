import Adam.Metadata
import Std.Tactic.RCases
import Adam.Options.MathlibPart

--set_option tactic.hygienic false

Game "Adam"
World "Proposition"
Level 12

Title "Oder"

Introduction
"
Der nächste bitte …
"

Statement
""
    (A B : Prop) (hA : A) : A ∨ (¬ B) := by
  Hint "**Du** Muss ich jetzt wieder das Beweisziel de-konstruieren?

**Robo** Nein, viel einfacher.  Wenn du eine Oder-Aussage beweisen sollst, musst du dich
einfach entscheiden, ob du die linke oder rechte Seite beweisen willst.

**Du** Und wie erkläre ich meinem Formalosophen, welche Seite ich gern beweisen würde?
Ich will natürlich `{A}` beweisen!

**Robo** Mit `left` bzw. `right`. Ist doch logisch, oder?"
  Branch
    right
    Hint "**Robo** Wusste gar nicht, dass du eine Links-Rechts-Schwäche hast.  Probier's nochmal."
  left
  assumption

Conclusion
"
Auch dieser Formalosoph zieht zufrieden von dannen.
"

NewTactic left right assumption
DisabledTactic tauto
