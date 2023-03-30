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
Level 3

Title "Widerspruch"

Introduction
"**Benedictus**: Hier ist noch eine Variante.
"

--   Eine sehr nützliche Beweismethode ist per Widerspruch.

-- Wir habe schon gesehen, dass `contradiction` einen Widerspruch in den Annahmen
-- sucht, und damit jegliches beweisen kann.

-- Um dorthin zu kommen, können wir `by_contra h` brauchen, welches das aktuelle
-- Goal auf `False` setzt und die Negierung des Goals als Annahme hinzufügt.

-- Insbesondere braucht man `by_contra h` meistens, wenn im Goal eine Negierung
-- steht:

Statement (A B : Prop) (g : A → B) (b : ¬ B) : ¬ A := by
  Hint "**Robo**: Ein `¬` im Goal heißt häufig, dass Du einen Widerspruchsbeweis führen
  möchtest.

  **Du**: Und wie mache ich das? Mit `contradiction`?

  **Robo**: Mit `by_contra h` fängst Du einen Widerspruchsbeweis an. Und mit `contradiction` schließt Du ihn ab."
  by_contra h
  Hint "**Robo**: Jetzt hast du also eine Annahme `{h} : {A}`, und damit musst Du einen Widerspruch herleiten.

  Du könntest zum Beispiel jetzt mit `suffices` sagten, welchen Widerspruch Du gern herleiten möchtest, etwa `suffices k : B`
  "
  suffices k : B
  Hint "**Du**: Ah, und jetzt kann ich einfach sagen dass sich die Annahmen `{B}` und `¬{B}` sich widersprechen."
  contradiction
  Hint "**Robo**: Und jetzt musst Du nur noch das Zwischenresultat herleiten, dass zu diesem Widerspruch geführt hat."
  apply g
  assumption

NewTactic by_contra

Conclusion "**Benedictus**:  Ich sehe schon, Ihr lernt schnell!"
