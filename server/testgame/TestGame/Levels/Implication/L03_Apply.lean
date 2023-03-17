import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Implication"
Level 3

Title "Apply"

Introduction
"
Sein Kollege zieht eine Linie unter deinen Beweis, schreibt ein durchgestrichenes ~`revert`~
hin und gibt dir das Blatt wieder.
"

Statement (A B : Prop) (hA : A) (h : A → B) : B := by
  Hint "**Robo**: Da hat er natürlich recht, normalerweise ist es viel schöner mit
  `apply {h}` die Implikation anzuwenden."
  apply h
  Hint "**Du**: Und jetzt genügt es also `A` zu zeigen."
  assumption

Conclusion "**Robo** Übrigens mit `apply LEMMA` kannst auch jedes Lemma anwenden, dessen
Aussage mit dem Goal übereinstimmt.

Die beiden Fragenden schauen das Blatt an und murmeln zustimmend."

NewTactic apply
DisabledTactic revert tauto

-- Katex notes
-- `\\(    \\)` or `$   $` for inline
-- and `$$  $$` block.
-- align block:
-- $$\\begin{aligned} 2x - 4 &= 6 \\\\ 2x &= 10 \\\\ x &= 5 \\end{aligned}$$
