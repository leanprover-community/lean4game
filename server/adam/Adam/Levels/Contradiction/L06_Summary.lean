import Adam.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import Adam.ToBePorted

Game "Adam"
World "Contradiction"
Level 6

Title "Contradiction"

Introduction
"
**Du**: Aber hätten wir die letzte Aufgabe nicht genauso gut per Widerspruch beweisen können?

**Benedictus**:  Klar.  Ich dachte nur, ein zweiter Widerspruchsbeweis wäre langweilig. Aber Ihr könnt die Aufgabe gern noch einmal probieren. Hier, ich gebe Sie Euch mit auf die Reise.  Aber nun seht zu, dass Ihr weiterkommt!"

-- Statt mit `contrapose`  `by_contra` ein Widerspruchsbeweis.
-- Probiers doch einfach!
-- In diesem Kapitel hast du also folgende Taktiken kennengelernt:


-- Als Vergleich zwischen Beweisen \"per Widerspruch\"
-- und \"per Kontraposition\", beweise die Gleiche Aufgabe indem
-- du mit `by_contra` einen Widerspruch suchst.

open Nat

Statement (n : ℕ) (h : Odd (n ^ 2)) : Odd n := by
  Hint "Sobald Ihr Euch sicher vom Gravitationsfeld des Asteroiden befreit habt, beugt Ihr Euch wieder über die Aufgabe.

  **Robo**:  Ok, also diesmal fangen wir mit `by_contra g` an!"
  by_contra g
  Hint "**Robo**: Jetzt würde ich einen Widerspruch zu `Odd (n ^ 2)` führen."
  Hint (hidden := true) "**Robo**: Also `suffices g : ¬ Odd (n ^ 2)`."
  suffices d : ¬ Odd (n ^ 2)
  contradiction
  rw [←even_iff_not_odd] at *
  apply even_square
  assumption

DisabledTactic contrapose revert

Conclusion "**Robo**: Bravo! Hier ein Überblick, was uns Benediktus gezeigt hat.


|       | Taktik          | Beispiel                                               |
|:------|:----------------|:-------------------------------------------------------|
| 17    | `have`          | Zwischenresultat annehmen                              |
| 18    | `suffices`      | Zwischenresultat annehmen                              |
| 19    | `by_contra`     | Widerspruch *(startet einen Widerspruchsbeweis)*       |
| *3*   | `contradiction` | *(schliesst einen Widerspruchsbeweis)*                 |
| 20    | `contrapose`    | Kontraposition                                         |
| *9*   | `revert`        | nützlich, um danach `contrapose` anzuwenden            |
"
