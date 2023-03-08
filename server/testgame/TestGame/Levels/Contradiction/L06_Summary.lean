import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import TestGame.ToBePorted

Game "TestGame"
World "Contradiction"
Level 6

Title "Contradiction"

Introduction
"
In diesem Kapitel hast du also folgende Taktiken kennengelernt:

|       | Taktik          | Beispiel                                               |
|:------|:----------------|:-------------------------------------------------------|
| 16    | `have`          | Zwischenresultat annehmen.                             |
| 17    | `suffices`      | Zwischenresultat annehmen.                             |
| 18    | `by_contra`     | Widerspruch. (startet einen Widerspruch)               |
| *3*   | `contradiction` | *(Schliesst einen Widerspruchsbeweis)*                 |
| 19    | `contrapose`    | Contraposition.                                        |
| *9*   | `revert`        | Nützlich um danach `contrapose` anzuwenden.            |

Als Vergleich zwischen Beweisen \"per Widerspruch\"
und \"per Kontraposition\", beweise die Gleiche Aufgabe indem
du mit `by_contra` einen Widerspruch suchst.
"

Statement
    "Ist n² ungerade, so ist auch n ungerade. Beweise durch Widerspruch."
    (n : ℕ) (h : Odd (n ^ 2)) : Odd n := by
  by_contra g
  suffices d : ¬ Odd (n ^ 2)
  contradiction
  rw [not_odd] at *
  apply even_square
  assumption

HiddenHint (n : ℕ) (h : Odd (n^2)) : Odd n =>
"Schreibe `by_contra h₁` um einen Beweis durch Widerspruch zu starten."

Hint (n : ℕ) (g : ¬ Odd n) (h : Odd (n^2)) : False =>
"
Am sinnvollsten ist es, hier einen Widerspruch zu `Odd (n^2)` zu suchen.
Dafür kannst du
```
suffices k : ¬ Odd (n ^ 2)
contradiction
```
benützen.
"

HiddenHint (n : ℕ) (g : ¬ Odd (n^2)) (h : Odd (n^2)) : False =>
"Hier brauchst du nur `contradiction`."

Hint (n : ℕ) (g : ¬ Odd n) (h : Odd (n^2)) : ¬ Odd (n^2) =>
"Das Zwischenresultat `¬Odd (n^2)` muss auch bewiesen werden.
Hier ist wieder das Lemma `not_Odd` hilfreich."

HiddenHint (n : ℕ) (g : ¬ Odd n) (h : Odd (n^2)) : Even (n^2) =>
"Mit `rw [not_Odd] at *` kannst du im Goal und allen Annahmen gleichzeitig umschreiben."

Hint (n: ℕ) (h : Odd (n ^ 2)) (g : Even n) : Even (n ^ 2) =>
"Diese Aussage hast du bereits als Lemma bewiesen."

HiddenHint (n: ℕ) (h : Odd (n ^ 2)) (g : Even n) : Even (n ^ 2) =>
"Probiers mit `apply ...`"


NewTactic contradiction by_contra rw apply assumption -- TODO: suffices, have
NewDefinition Even Odd
NewLemma not_odd not_even even_square
