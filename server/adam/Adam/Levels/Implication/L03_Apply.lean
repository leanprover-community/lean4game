import Adam.Metadata
import Mathlib

Game "Adam"
World "Implication"
Level 3

Title "Apply"

Introduction
"
Leider läuft das Telefonat nicht so gut.  Er legt wieder auf und schüttelt mit dem Kopf.

**Operationsleiter**: Der Kollege auf der anderen Seite des Mondes versteht kein `revert`. Oder er tut zumindest so.  Habt Ihr noch eine andere Idee? 

Er zieht eine Linie unter Euren Beweis, ergänzt ein durchgestrichenes ~`revert`~, und legt Euch das Blatt ein zweites Mal vor.
"

Statement (A B : Prop) (hA : A) (h : A → B) : B := by
  Hint "**Robo**:  Vielleicht wäre es ohnehin eleganter gewesen, mit Implikation mit `apply {h}` anzuwenden."
  apply h
  Hint "**Du**: Ja, das kommt mir jetzt auch natürlich vor."
  assumption

Conclusion "Diesmal scheint das Telefont erfolgreich zu verlaufen."

NewTactic apply
DisabledTactic revert tauto

-- Katex notes
-- `\\(    \\)` or `$   $` for inline
-- and `$$  $$` block.
-- align block:
-- $$\\begin{aligned} 2x - 4 &= 6 \\\\ 2x &= 10 \\\\ x &= 5 \\end{aligned}$$
