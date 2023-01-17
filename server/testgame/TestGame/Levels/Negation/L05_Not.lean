import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Implication"
Level 20

Title "Nicht-nicht"

Introduction
"
Wenn man ein Nicht (`¬`) im Goal hat, will man meistens einen Widerspruch starten,
wie im nächsten Level dann gezeigt wird. Manchmal aber hat man Terme der Form
`¬ (¬ A)`, in welchem Fall das Lemma `not_not` nützlich ist, welches du mit
`rw` oder `apply` benützen kannst.
"

Statement
    "Zeige, dass $\\neg(\\neg A)$ äquivalent zu $A$ ist."
    (A : Prop) : ¬ (¬ A) ↔ A := by
  rw [not_not]

Message (A : Prop) : ¬ (¬ A) ↔ A => "Da `not_not` ein Lemma der Form `X ↔ Y` ist,
kannst du wahlweise `rw [not_not]` oder `apply not_not` benützen.

- `rw` ersetzt `¬ (¬ A)` mit `A` und schliesst dann `A ↔ A` mit `rfl`.
- `apply` hingegen funktioniert hier nur, weil das gesamte Goal
genau mit der Aussage des Lemmas übereinstimmt.
"

Tactics rw apply

Lemmas not_not
