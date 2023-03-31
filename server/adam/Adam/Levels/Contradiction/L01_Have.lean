import Adam.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import Adam.ToBePorted

set_option tactic.hygienic false

Game "Adam"
World "Contradiction"
Level 1

Title "Was wir haben, haben wir."

Introduction
"
**Benedictus**:  Hier, schaut mal.  Das habe ich für Euch vorbereitet.
"

-- Manchmal, wollen wir nicht am aktuellen Goal arbeiten, sondern zuerst ein
-- Zwischenresultat beweisen, welches wir dann benützen können.

-- Mit `have [Name] : [Aussage]` kann man ein Zwischenresultat erstellen,
-- dass man anschliessen beweisen muss.

-- Wenn du zum Beispiel die Annahmen `(h : A → ¬ B)` und `(ha : A)` hast, kannst
-- du mit
-- ```
-- have g : ¬ B
-- apply h
-- assumption
-- ```
-- eine neue Annahme `(g : ¬ B)` erstellen. Danach beweist du zuerst diese Annahme,
-- bevor du dann mit dem Beweis forfährst.

Statement (A B : Prop) (h : A → ¬ B) (k : A ∧ B) : False := by
  Hint "**Du**: Also als erstes teile ich wohl mal das Und (`∧`) auf."
  rcases k with ⟨h₁, h₂⟩
  Hint "**Du**: Und jetzt …

  **Benedictus**: … solltest du dir ein passendes Zwischenresultat zurechtlegen.

  **Robo**:  Ja!  Probier mal `have g : ¬ B`!"
  have g : ¬ B
  · Hint "**Du**: Was?  Jetzt hab ich einfach angenommen, dass sei richtig?

    **Robo**: Nee, jetzt musst du das erst noch beweisen, bevor du es dann benutzen kannst."
    Hint (hidden := true) "**Robo**: `apply` sollte helfen"
    apply h
    assumption
  Hint "**Du**: Und wie war das nochmals wenn zwei Annahmen sich widersprechen?

  **Robo**: `contradiction`."
  contradiction

NewTactic «have»
DisabledTactic «suffices»

Conclusion "**Benedictus**: Das sieht gut aus!"
