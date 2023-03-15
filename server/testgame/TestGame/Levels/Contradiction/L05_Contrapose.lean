import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import TestGame.ToBePorted

Game "TestGame"
World "Contradiction"
Level 5

Title "Kontraposition"

Introduction
"
*Oddeus* reicht euch das Papier.

**Du**: Da steht etwas über `contrapose` hier…

**Oddeus**: Das ist doch klar eine Aggression uns gegenüber!

**Robo**: Wartet mal, vielleicht wollte euch eure Schwester einfach von ihren neuen
Endeckungen zeigen. Schaut, darunter ist eine Aufgabe.
"

-- Ein Beweis durch Kontraposition benützt im Grunde das eben bewiesene Lemma

-- ```
-- lemma not_imp_not (A B : Prop) : (A → B) ↔ (¬ B → ¬ A) := by
--   [...]
-- ```

-- Dazu gibt es die Taktik `contrapose`, welche eine Implikation im Goal
-- entsprechend umdreht.

-- Wir erinnern hier an die Taktik `revert h`, die aus der Annahme `h` eine Implikation
-- im Goal erstellt.

-- Im Gegensatz dazu kann man auch einen Beweis durch Kontraposition führen.
-- Das ist kein Widerspruch, sondern benützt dass `A → B` und `(¬ B) → (¬ A)`
-- logisch equivalent sind.

-- Wenn das Goal eine Implikation ist, kann man `contrapose` anwenden.

Statement (n : ℕ) (h : Odd (n ^ 2)): Odd n := by
  Hint "**Oddeus**: Wie soll das den gehen?

  **Robo**: `contrapose` benutzt das Lemma eurer Gelehrter, `not_imp_not`. Also es wandelt
  ein Goal `A → B` zu `¬B → ¬A ` um.

  **Du**: Aber das Goal ist doch gar keine Implikation?

  **Robo**: Mit `revert {h}` kannst du die Annahme `{h}` als Implikationsannahme ins Goal
  schieben."
  revert h
  Hint "*Oddeus*: Ob man jetzt wohl dieses `contrapose` benutzen kann?"
  contrapose
  Hint (hidden := true) "**Du**: Warte mal, jetzt kann man wohl `not_odd` verwenden…"
  rw [not_odd]
  rw [not_odd]
  Hint "**Robo**: Und den Rest hast du bei *Evenine* als Lemma gezeigt!"
  apply even_square

NewTactic contrapose
DisabledTactic by_contra

Conclusion "**Oddeus**: Ah ich sehe, die Aussage ist, dass wir das nur zusammen lösen konnten.
Ich danke euch, darauf wäre ich nie gekommen."
