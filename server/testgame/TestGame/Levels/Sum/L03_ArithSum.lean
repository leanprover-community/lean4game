import TestGame.Metadata

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

import TestGame.Options.BigOperators

set_option tactic.hygienic false

Game "TestGame"
World "Sum"
Level 3

Title "Arithmetische Summe"

Introduction
"
Oft beweist man Aussagen über Summen am besten per Induktion.

Mit `induction n` startet man einen Induktionsbeweis. Dies erstellt 2 neue Goals:

* **Induktionsanfang**: `n = 0`. Dieser kann ganz oft direkt mit `simp` bewiesen werden.
* **Induktionsschritt**: Man kriegt eine Annahme `(n_ih : P n)` und muss `P (n + 1)`
  beweisen. Für endliche Summen will man normalerweise danach zuerst
  `rw [Fin.sum_univ_castSucc]` brauchen, welches
  $$\\sum_{i=0}^{n} a_i = \\sum_{i=0}^{n-1} a_i + a_n$$
  umschreibt.

**Bemerkung:**

Eine technische Sonderheit bezüglich endlichen Summen
ist der kleine Pfeil `↑` in `∑ i : Fin (n + 1), ↑i`.
Da `i : Fin n` technisch keine natürliche Zahl ist (sondern vom Typ `Fin n`), muss man
dieses zuerst mit `↑i` oder `(i : ℕ)` in eine natürliche Zahl umwandeln. Diese nennt man
*Coersion*.

Gleichermassen, kommen hier im Induktionsschritt die Terme `↑(↑Fin.castSucc.toEmbedding i)`
und `↑(Fin.last (n + 1))` vor. Diese Terme können mit `simp` vereinfacht werden.
"

open BigOperators

Statement arithmetic_sum
"Zeige $2 \\cdot \\sum_{i = 0}^n i = n \\cdot (n + 1)$."
    (n : ℕ) : 2 * (∑ i : Fin (n + 1), ↑i) = n * (n + 1) := by
  induction n
  simp
  rw [Fin.sum_univ_castSucc]
  rw [mul_add]
  simp
  rw [n_ih]
  rw [Nat.succ_eq_add_one]
  ring

NewTactics induction
NewLemmas Fin.sum_univ_castSucc Nat.succ_eq_add_one mul_add add_mul

Hint (n : ℕ) : 2 * (∑ i : Fin (n + 1), ↑i) = n * (n + 1) =>
"Als Erinnerung, einen Induktionsbeweis startet man mit `induction n`."

Hint : 2 * ∑ i : Fin (Nat.zero + 1), ↑i = Nat.zero * (Nat.zero + 1) =>
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
$$2 \\cdot ((\\sum_\{x=0}^n x) + (n + 1)) = 2 \\cdot \\sum_\{x=0}^n x + 2 \\cdot (n + 1))$$
umschreiben. Dazu kannst du `mul_add` benützen.
"

Hint (n : ℕ) (hn : 2 * ∑ i : Fin (n + 1), ↑i = n * (n + 1)) :
  2 * ∑ x : Fin (n + 1), ↑x + 2 * (n + 1) = Nat.succ n * (Nat.succ n + 1) =>
"`simp` vereinfacht `↑(↑Fin.castSucc.toEmbedding i)` zu `↑i`.
Danach kann die Induktionshypothese mit `rw` angewendet werden."

Hint (n : ℕ) (hn : 2 * ∑ i : Fin (n + 1), ↑i = n * (n + 1)) :
  n * (n + 1) + 2 * (n + 1) = Nat.succ n * (Nat.succ n + 1) =>
"
Im Moment muss man hier `ring` noch helfen,
indem man mit `rw [Nat.succ_eq_add_one]` zuerst `Nat.succ n = n + 1` umschreibt.

(Dies wird irgendwann noch gefixt)
"
