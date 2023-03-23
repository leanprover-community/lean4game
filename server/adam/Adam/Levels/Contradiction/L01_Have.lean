import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import TestGame.ToBePorted

Game "TestGame"
World "Contradiction"
Level 1

Title "Have"

Introduction
"
**Oddeus**: Willkommen Reisende! Ich muss eingestehen ich bin in Gedanken noch
an etwas, könnt ihr mir bei diesem widersprüchlichen Problem helfen?
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
  Hint "**Du**: Also als erstes Teile ich wohl mal das Und (`∧`) auf."
  rcases k with ⟨h₁, h₂⟩
  Hint "**Du**: Aber jetzt…

  **Robo**: Du könntest dir ein passendes Zwischenresultat zurechtlegen, das dir hilft:
  Mach mal `have g : ¬ B`!"
  have g : ¬ B
  · Hint "**Du**: Was und jetzt hab ich einfach angenommen das sei richtig?

    **Robo**: Ne, jetzt musst du das zuerst beweisen bevor du es dann benützen kannst."
    Hint (hidden := true) "**Robo**: `apply` scheint passend zu sein."
    apply h
    assumption
  · Hint (hidden := true) "**Du**: Und wie war das nochmals wenn zwei Annahmen sich widersprechen?

    **Robo**: `contradiction`."
    contradiction

NewTactic «have»
DisabledTactic «suffices»

Conclusion "*Oddeus*: Das stimmt wohl."
