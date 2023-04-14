import Adam.Metadata
import Std.Tactic.RCases

import Adam.ToBePorted
import Adam.Levels.Predicate.L06_Exists

Game "Adam"
World "Contradiction"
Level 5

Title "Kontraposition"

Introduction
"
**Benedictus**:  Gut, hier ist die angekündigte Frage.  Versucht mal einen *direkten* Beweis, ohne `by_contra`.
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
open Nat

Statement (n : ℕ) (h : Odd (n ^ 2)): Odd n := by
  Hint "**Robo**: Ich schlage vor, wir führen das auf das Lemma `even_square` zurück, das wir auf Quantus schon gezeigt hatten.  Hier steht ja im Grunde `Odd (n^2) → Odd n`.  Und unter Kontraposition ist das äquivalent zu `Even n → Even (n^2)`.

  **Du**:  Richtig. Von hinten durch die Brust … Aber warte, im Moment steht da doch gar kein `→`.

  **Robo**:  Erinner dich an `revert`.  Mit `revert {h}` kannst du die Annahme `{h}` als Implikationsannahme ins Beweissziel schieben."
  revert h
  Hint "**Du**: Und jetzt kann ich dieses Kontrapositionslemma anwenden?  Wie hieß das noch einmal?

  **Robo**: Tatsächlich kannst auch einfach `contrapose` schreiben.
  "
  contrapose
  Hint (hidden := true) "**Robo**: Vielleicht hilft jetzt `even_iff_not_odd` weiter?"
  rw [← even_iff_not_odd]
  rw [← even_iff_not_odd]
  Hint "**Du**:  Das sieht schon ganz gut aus.  Jetzt kann ich tatsächlich das alte Lemma
  `even_square` anwenden!"
  apply even_square

NewTactic contrapose
DisabledTactic by_contra
LemmaTab "Nat"

Conclusion "**Benedictus**: Hervorragend!  Ich glaube, damit seid Ihr jetzt ganz gut gewappnet."
