import TestGame.Metadata

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

Game "TestGame"
World "Sum"
Level 3

Title "Arithmetische Summe"

Introduction
"
Oft beweist man Aussagen über Summen am besten per Induktion.

Eines der wichtigsten Lemmas für den Induktionsschritt ist
`Fin.sum_univ_castSucc`, welches
$\\sum_{i=0}^{n} a_i = \\sum_{i=0}^{n-1} a_i + a_n$ umschreibt.

**Bemerkung:**

Eine technische Sonderheit ist der kleine Pfeil `↑` in `∑ i : Fin (n + 1), ↑i`.
Da `i : Fin n` technisch keine natürliche Zahl ist (sondern vom Typ `Fin n`), muss man
dieses zuerst mit `↑i` oder `(i : ℕ)` in eine natürliche Zahl umwandeln. Diese nennt man
*Coersion*.

Gleichermassen, kommen hier im Induktionsschritt die Terme `↑(↑Fin.castSucc.toEmbedding i)`
und `↑(Fin.last (n + 1))` vor. Diese Terme können mit `simp` vereinfacht werden.
"

-- Note: I don't want to deal with Nat-division, so I stated it as `2 * ... = ...` instead.

set_option tactic.hygienic false

open BigOperators

Statement arithmetic_sum
"Zeige $2 \\cdot \\sum_{i = 0}^n i = n \\cdot (n + 1)$."
    (n : ℕ) : 2 * (∑ i : Fin (n + 1), ↑i) = n * (n + 1) := by
  induction' n with n hn
  simp
  rw [Fin.sum_univ_castSucc]
  rw [mul_add]
  simp
  rw [hn]
  rw [Nat.succ_eq_add_one]
  ring

NewTactics ring
NewLemmas Fin.sum_univ_castSucc Nat.succ_eq_add_one mul_add add_mul

Hint (n : ℕ) : 2 * (∑ i : Fin (n + 1), ↑i) = n * (n + 1) =>
"Als Erinnerung, einen Induktionsbeweis startet man mit `induction n`."

Hint (n : ℕ) : 2 * ∑ i : Fin (0 + 1), ↑i = 0 * (0 + 1) =>
"Den Induktionsanker $n = 0$ kann `simp` oft beweisen."

Hint (n : ℕ) (hn : 2 * ∑ i : Fin (n + 1), ↑i = n * (n + 1)) :
  2 * ∑ i : Fin (Nat.succ n + 1), ↑i = Nat.succ n * (Nat.succ n + 1) =>
"Den Induktionsschritt beginnt man oft mit `rw [Fin.sum_univ_castSucc]`."

-- Hint (n : ℕ) (hn : 2 * ∑ i : Fin (n + 1), ↑i = n * (n + 1)) :
--   2 * (∑ i : Fin (n + 1), ↑(Fin.castSucc.toEmbedding i) +
--   ↑(Fin.last (n + 1))) = Nat.succ n * (Nat.succ n + 1) =>
-- "Die Taktik `simp` vereinfacht `↑(↑Fin.castSucc.toEmbedding i)`. "

Hint (n : ℕ) (hn : 2 * ∑ i : Fin (n + 1), ↑i = n * (n + 1)) :
  2 * (∑ x : Fin (n + 1), ↑x + (n + 1)) = Nat.succ n * (Nat.succ n + 1) =>
"Um Die Induktionshypothese anzuwenden muss man noch
$$2 \\cdot ((\\sum_{x=0}^n x) + (n + 1)) = 2 \\cdot \\sum_{x=0}^n x + 2 \\cdot (n + 1))$$
umschreiben. Dazu kannst du `mul_add` benützen.
"

Hint (n : ℕ) (hn : 2 * ∑ i : Fin (n + 1), ↑i = n * (n + 1)) :
  2 * ∑ x : Fin (n + 1), ↑x + 2 * (n + 1) = Nat.succ n * (Nat.succ n + 1) =>
"Jetzt kann die Induktionshypothese mit `rw` angewendet werden."

Hint (n : ℕ) (hn : 2 * ∑ i : Fin (n + 1), ↑i = n * (n + 1)) :
  n * (n + 1) + 2 * (n + 1) = Nat.succ n * (Nat.succ n + 1) =>
"
Im Moment muss man hier `ring` noch helfen,
indem man mit `rw [Nat.succ_eq_add_one]` zuerst `Nat.succ n = n + 1` umschreibt.

(Dies wird irgendwann noch gefixt)
"
