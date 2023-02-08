import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Implication"
Level 3

Title "Apply"

Introduction
"
`revert` ist aber nur selten der richtige Weg.

Im vorigen Beispiel würde man besser die Implikation $A \\Rightarrow B$ *anwenden*, also
sagen \"Es genügt $A$ zu zeigen, denn $A \\Rightarrow B$\" und danach $A$ beweisen.

Wenn man eine Implikation `(g : A → B)` in den Annahmen hat, bei welcher die Konsequenz
(also $B$) mit dem Goal übereinstimmt, kann man `apply g` genau dies machen.
"

Statement
    "Seien $A, B$ logische Aussagen, wobei $A$ wahr ist und $A \\Rightarrow B$.
    Zeige, dass $B$ wahr ist."
    (A B : Prop) (hA : A) (g : A → B) : B := by
  apply g
  assumption

HiddenHint (A : Prop) (B : Prop) (hA : A) (g : A → B) : B =>
"Mit `apply g` kannst du die Implikation `g` anwenden."

HiddenHint (A : Prop) (B : Prop) (hA : A) (g : A → B) : A =>
"Nachdem du die Implikation `A → B` angewendet hast, musst du nur noch $A$ zeigen,
dafür hast du bereits einen Beweis in den Annahmen."

NewTactics apply assumption

-- Katex notes
-- `\\(    \\)` or `$   $` for inline
-- and `$$  $$` block.
-- align block:
-- $$\\begin{aligned} 2x - 4 &= 6 \\\\ 2x &= 10 \\\\ x &= 5 \\end{aligned}$$
