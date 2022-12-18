import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Logic"
Level 7

Title "Implikation"

Introduction
"Als nächstes widmen wir uns der Implikation $A \\Rightarrow B$.
Mit zwei logischen Aussagen `(A : Prop) (B : Prop)` schreibt man eine Implikation
als `A → B` (`\\to`).

Wenn man als Goal $B$ beweisen möchte und eine Impikation `(g : A → B)`
hat, kann man mit `apply g` diese
anwenden, worauf das zu beweisende Goal $A$ wird. Auf Papier würde man an der Stelle
folgendes zu schreiben: \"Es genügt $A$ zu zeigen, denn $A \\Rightarrow B$\".

*Bemerke:* Das ist der selbe Pfeil, der später auch für Funktionen wie `ℕ → ℕ` gebraucht
wird, deshalb heisst er `\\to`."


Statement
    "Seien $A, B$ logische Aussagen, wobei $A$ wahr ist und $A \\Rightarrow B$.
    Zeige, dass $B$ wahr ist."
    (A B : Prop) (hA : A) (g : A → B) : B := by
  apply g
  assumption

Hint (A : Prop) (B : Prop) (hA : A) (g : A → B) : B =>
"Mit `apply g` kannst du die Implikation `g` anwenden."

Hint (A : Prop) (B : Prop) (hA : A) (g : A → B) : A =>
"Nachdem du die Implikation `A → B` angewendet hast, musst du nur noch $A$ zeigen,
dafür hast du bereits einen Beweis in den Annahmen."

Tactics apply assumption

-- Katex notes
-- `\\(    \\)` or `$   $` for inline
-- and `$$  $$` block.
-- align block:
-- $$\\begin{aligned} 2x - 4 &= 6 \\\\ 2x &= 10 \\\\ x &= 5 \\end{aligned}$$
