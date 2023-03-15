import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring
import Mathlib

import TestGame.ToBePorted

Game "TestGame"
World "Contradiction"
Level 3

Title "Per Widerspruch"

Introduction
"**Oddeus**: Ich verstehe *Evenine* einfach nicht. Ich will euch auch gleich zeigen,
was sie mir letzthin geschrieben hat, aber zuerst schaut einmal unseren
wunderschönen Absurda-Tempel an!

Damit kommt ihr vor einen sehr hohen Turm, der ausschliesslich aus Dornenranken gewachsen
scheint.

**Oddeus**: Versteht ihr, was hier über dem Eingang steht?
"

--   Eine sehr nützliche Beweismethode ist per Widerspruch.

-- Wir habe schon gesehen, dass `contradiction` einen Widerspruch in den Annahmen
-- sucht, und damit jegliches beweisen kann.

-- Um dorthin zu kommen, können wir `by_contra h` brauchen, welches das aktuelle
-- Goal auf `False` setzt und die Negierung des Goals als Annahme hinzufügt.

-- Insbesondere braucht man `by_contra h` meistens, wenn im Goal eine Negierung
-- steht:

Statement (A B : Prop) (g : A → B) (b : ¬ B) : ¬ A := by
  Hint "**Robo**: Ein `¬` im Goal heisst häufig, dass du einen Widerspruchsbeweis führen
  möchtest.

  **Du**: Und wie mach ich das? Mit `contradiction`?

  **Robo**: Mit `by_contra h` fängst du einen an. Mit `contradiction` schliesst du ihn dann
  später ab."
  by_contra h
  Hint "**Robo**: Jetzt hast du also eine Annahme `{h} : ¬ {A}`, und damit musst du einen
  Widerspruch herbeileiten.

  Ein Methode ist, dass du jetzt mit `suffices` sagts, zu was du denn gerne den Widerspruch
  haben möchtest, zum Beispiel `suffices k : B`
  "
  suffices k : B
  Hint "**Du**: Ah und jetzt kann ich einfach sagen dass sich die Anahmen `{B}` und `¬{B}`
  widersprechen."
  contradiction
  Hint "**Robo**: Und jetzt kannst du noch das Ergebnis zeigen, das zu einem Widerspruch
  geführt hat."
  apply g
  assumption

NewTactic by_contra

Conclusion "**Oddeus**: Sehr gut, kommt mit hinein!"
