import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Contradiction"
Level 5

Title "Nicht-nicht"

Introduction
"
Wenn man ein Nicht (`¬`) im Goal hat, will man meistens einen Widerspruch starten,
wie im nächsten Level dann gezeigt wird. Manchmal aber hat man Terme der Form
`¬ (¬ A)`, in welchem Fall das Lemma `not_not` nützlich ist.
"

Statement
    (A : Prop) : ¬ (¬ A) ↔ A := by
  rw [not_not]

Tactics rw

Lemmas not_not
