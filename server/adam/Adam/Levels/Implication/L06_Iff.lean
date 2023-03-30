import Adam.Metadata

Game "Adam"
World "Implication"
Level 6

Title "Genau dann, wenn"

Introduction
"
**Operationsleiter:** Wir hatten auch mal ein paar Förderbänder, die in beide Richtungen laufen konnten.  Die hatte ich vorsichtshalber alle abgestellt, weil in den neusten Handbüchern von solchen Doppelbändern abgeraten wird.  Aber vielleicht sind sie ja unter bestimmten Voraussetzungen doch sicher?  Was meint Ihr zu diesem Fall?
"

Statement (A B : Prop) (mp : A → B) (mpr : B → A) : A ↔ B := by
  Hint "**Robo**: `→` ist natürlich Leansch für `$\\iff$`.
  Die Aussage `A ↔ B` besteht also aus zwei Teilen; sie ist als `⟨A → B, B → A⟩` definiert.

  **Du**: Also ganz ähnlich wie das UND, `A ∧ B`?

  **Robo**: Genau. Entsprechend kannst Du auch hier mit `constructor` anfangen."
  constructor
  Hint "**Du**: Ah, und die beiden Teile habe ich schon in den Annahmen."
  assumption
  assumption

Conclusion
"
**Operationsleiter**: Ok, das leuchtet mir ein.

**Robo** *(zu Dir)*: Übrigens, so wie bei `(h : A ∧ B)` die beiden Teile `h.left` und `h.right` heißen,
heißen bei `(h : A ↔ B)` die beiden Teile `h.mp` und `h.mpr`.

**Du**: Also `h.mp` ist `A → B`? Wieso `mp`?

**Robo**: `mp` steht für Modus Ponens`.  Der Modus ponens ist eine schon in der antiken Logik geläufige Schlussfigur, die in vielen logischen Systemen …  Ach nee, das wolltest Du ja nicht hören.  Das \"r\" in `mpr` steht für \"reverse\", weil's die Rückrichtung ist.
"

NewTactic constructor
DisabledTactic tauto rw

-- TODO : `case mpr =>` ist mathematisch noch sinnvoll.
