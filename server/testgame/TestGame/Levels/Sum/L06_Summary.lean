import TestGame.Metadata

import TestGame.Options.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

import TestGame.ToBePorted
import TestGame.Options.ArithSum

Game "TestGame"
World "Sum"
Level 6

set_option tactic.hygienic false

Title "Zusammenfassung"

Introduction
"
Zusammenfassung aus diesem Kapitel

## Notationen / Begriffe

|                      | Beschreibung                              |
|:---------------------|:------------------------------------------|
| `Fin n`              | Ist ein Typ mit Zahlen $0, \\ldots, n-1$. |
| `∑ (i : Fin n), a i` | $\\sum_{i=0}^{n-1} a_i$                   |

## Taktiken

|    | Taktik                    | Beispiel                             |
|:---|:--------------------------|:-------------------------------------|
| 20 | `simp`                    | Simplifikation.                      |
| 21 | `induction n`             | Induktion über $n$                   |

Und hier noch eine etwas schwierigere Übung.

Das Resultat aus Level 3 kannst du als `arithmetic_sum` wiederverwenden:
$$
2 \\cdot \\sum_{i = 0}^n i = n \\cdot (n + 1)
$$
"

open BigOperators

Statement
"Zeige $\\sum_{i = 0}^m i^3 = (\\sum_{i = 0}^m i)^2$."
  (m : ℕ) : (∑ i : Fin (m + 1), (i : ℕ)^3) = (∑ i : Fin (m + 1), (i : ℕ))^2 := by
  induction' m with m hm
  simp
  rw [Fin.sum_univ_castSucc]
  simp
  rw [hm]
  rw [Fin.sum_univ_castSucc (n := m + 1)]
  simp
  rw [add_pow_two]
  rw [arithmetic_sum]
  ring

NewLemmas arithmetic_sum add_pow_two

HiddenHint (m : ℕ) : ∑ i : Fin (m + 1), (i : ℕ) ^ 3 = (∑ i : Fin (m + 1), ↑i) ^ 2 =>
"Führe auch hier einen Induktionsbeweis."

HiddenHint : ∑ i : Fin (Nat.zero + 1), (i : ℕ) ^ 3 = (∑ i : Fin (Nat.zero + 1), ↑i) ^ 2 =>
"`simp` kann den Induktionsanfang beweisen."

Hint (m : ℕ) : ∑ i : Fin (Nat.succ m + 1), (i : ℕ) ^ 3 = (∑ i : Fin (Nat.succ m + 1), ↑i) ^ 2 =>
"Im Induktionsschritt willst du das Goal so umformen, dass du folgende Therme
ersetzen kannst:

* `∑ i : Fin (m + 1), ↑i ^ 3` (Induktionshypothese)
* `2 * (∑ i : Fin (m + 1), ↑i)` (arithmetische Summe)
"

HiddenHint (m : ℕ) : ∑ i :
    Fin (Nat.succ m + 1), (i : ℕ) ^ 3 = (∑ i : Fin (Nat.succ m + 1), ↑i) ^ 2 =>
"
Als erstes kannst du mal mit dem bekannten `rw [Fin.sum_univ_castSucc]` anfangen.
"

HiddenHint (m : ℕ) : ∑ i : Fin (m + 1), (Fin.castSucc.toEmbedding i : ℕ) ^ 3 +
    ↑(Fin.last (m + 1)) ^ 3 = (∑ i : Fin (Nat.succ m + 1), ↑i) ^ 2 =>
"Mit `simp` kriegst du das `↑(Fin.castSucc.toEmbedding i)` weg"

Hint (m : ℕ) : ∑ x : Fin (m + 1), (x : ℕ) ^ 3 + (m + 1) ^ 3 =
    (∑ i : Fin (Nat.succ m + 1), ↑i) ^ 2 =>
"Jetzt kannst du die Induktionshypothese benützen."

Hint (m : ℕ) : (∑ i : Fin (m + 1), (i : ℕ)) ^ 2 + (m + 1) ^ 3 = (∑ i : Fin (Nat.succ m + 1), ↑i) ^ 2 =>
"Die linke Seite ist jetzt erst mal gut. Um auf der rechten Seite `Fin.sum_univ_castSucc`
anzuwenden, haben wir ein Problem: Lean schreibt immer die erste Instanz um, also würde gerne
auf der linken Seite `(∑ i : Fin (m + 1), ↑i) ^ 2` umschreiben.

Wir können Lean hier weiterhelfen, indem wir manche Argemente von `Fin.sum_univ_castSucc`
explizit angeben. Die Funktion hat ein Argument mit dem Namen `n`, welches wir z.B. explizit
angeben können:

```
rw [Fin.sum_univ_castSucc (n := m + 1)]
```
"

HiddenHint (m : ℕ) : (∑ i : Fin (m + 1), ↑i) ^ 2 + (m + 1) ^ 3 =
    (∑ i : Fin (m + 1), ↑(Fin.castSucc.toEmbedding i) + ↑(Fin.last (m + 1))) ^ 2 =>
"Wenn du noch einen AUsdruck `↑(Fin.castSucc.toEmbedding i)` hast, solltest du mal
`simp` aufrufen."

Hint (m : ℕ) : (∑ i : Fin (m + 1), ↑i) ^ 2 + (m + 1) ^ 3 = (∑ i : Fin (m + 1), ↑i + (m + 1)) ^ 2 =>
"Die rechte Seite hat die Form $(a + b)^2$ welche mit `add_pow_two` zu $a^2 + 2ab + b^2$
umgeschrieben werden kann."

HiddenHint (m : ℕ) : (∑ i : Fin (m + 1), ↑i) ^ 2 + (m + 1) ^ 3 =
    (∑ i : Fin (m + 1), ↑i) ^ 2 + (2 * ∑ i : Fin (m + 1), ↑i) * (m + 1) + (m + 1) ^ 2 =>
"Wenn du noch einen AUsdruck `↑(Fin.castSucc.toEmbedding i)` hast, solltest du mal
`simp` aufrufen."

Hint (m : ℕ) : (∑ i : Fin (m + 1), ↑i) ^ 2 + (m + 1) ^ 3 =
    (∑ i : Fin (m + 1), ↑i) ^ 2 + (2 * ∑ i : Fin (m + 1), ↑i) * (m + 1) + (m + 1) ^ 2 =>
"Jetzt hast du in der Mitte `2 * ∑ i : Fin (m + 1), ↑i)`, welches du mit der
arithmetischen Summe `arithmetic_sum` umschreiben kannst."

Hint (m : ℕ) : (∑ i : Fin (m + 1), ↑i) ^ 2 + (m + 1) ^ 3 =
    (∑ i : Fin (m + 1), ↑i) ^ 2 + m * (m + 1) * (m + 1) + (m + 1) ^ 2 =>
"Den Rest sollte `ring` für dich übernehmen."
