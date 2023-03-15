import TestGame.Metadata

Game "TestGame"
World "Implication"
Level 6

Title "Genau dann wenn"

Introduction
"
Als erstes kommt ihr in einen kleinen Raum mit ganz vielen Bildschirmen.

Ein junges Wesen dreht sich auf dem Stuhl um, und sagt:

**Mitarbeiter**: Oh hallo! Schaut euch mal das hier an!
"

Statement (A B : Prop) (mp : A → B) (mpr : B → A) : A ↔ B := by
  Hint "**Robo**: Das ist ein genau-dann-wenn Pfeil: `\\iff`. Er besteht aus zwei Teilen:
  `A ↔ B` ist als `⟨A → B, B → A⟩` definiert.

  **Du**: Also ganz ähnlich wie das UND, `A ∧ B`?

  **Robo**: Genau. Entsprechend kannst du hier auch mit `constructor` anfangen."
  constructor
  Hint "**Du**: Ah und die beiden hab ich schon in den Annahmen."
  assumption
  assumption

Conclusion
"
**Robo**: Übrigens, bei `(h : A ∧ B)` haben die beiden Teile `h.left` und `h.right` geheissen,
hier bei `(h : A ↔ B)` heissen sie `h.mp` und `h.mpr`.

**Du**: Also `h.mp` ist `A → B`? Wieso `mp`?

**Operationsleiter**: \"Modulo Ponens\" ist ein lokaler Begriff hier,
aber das ist doch nicht wichtig.

**Robo**: Und das \"r\" in `mpr` stünde für \"reverse\" weil's die Rückrichtung ist.
"

NewTactic constructor
DisabledTactic tauto rw

-- TODO : `case mpr =>` ist mathematisch noch sinnvoll.
