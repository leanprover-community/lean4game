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
`revert` ist aber nur selten der richtige Weg.

Im vorigen Beispiel würde man besser die Implikation $A \\Rightarrow B$ *anwenden*, also
sagen \"Es genügt $A$ zu zeigen, denn $A \\Rightarrow B$\" und danach $A$ beweisen.

Wenn man eine Implikation `(g : A → B)` in den Annahmen hat, bei welcher die Konsequenz
(also $B$) mit dem Goal übereinstimmt, kann man `apply g` genau dies machen.
"

Statement (A B : Prop) (hA : A) (h : A → B) : B := by
  Hint "**Robo**: Du hast natürlich recht, normalerweise ist es viel schöner mit
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
