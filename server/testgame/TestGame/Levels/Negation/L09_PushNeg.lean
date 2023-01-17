import TestGame.Metadata
import Mathlib.Tactic.PushNeg
import Mathlib

import TestGame.ToBePorted

Game "TestGame"
World "Predicate"
Level 9

Title "PushNeg"

Introduction
"
Zum Schluss, immer wenn man irgendwo eine Verneinung `¬∃` oder `¬∀` sieht (`\\not`), kann man
mit `push_neg` das `¬` durch den Quantor hindurchschieben.

Das braucht intern die Lemmas

- `not_exists (A : Prop) : ¬ (∃ x, A) ↔ ∀x, (¬A)`
- `not_forall (A : Prop) : ¬ (∀ x, A) ↔ ∃x, (¬A)`

(welche man auch mit `rw` explizit benutzen könnte.)
"

Statement
    "Es existiert keine natürliche Zahl $n$, sodass $n + k$ immer ungerade ist.":
    ¬ ∃ (n : ℕ), ∀ (k : ℕ) , odd (n + k) := by
  push_neg
  intro n
  use n
  rw [not_odd]
  unfold even
  use n
  ring

Message : ¬ ∃ (n : ℕ), ∀ (k : ℕ) , odd (n + k) =>
"`push_neg` schiebt die Negierung an den Quantoren vorbei."


Message (n : ℕ) : (∃ k, ¬odd (n + k)) =>
"An dieser Stelle musst du nun ein `k` angeben, sodass `n + k` gerade ist... Benutze `use`
mit der richtigen Zahl."


Hint (n : ℕ) : ¬odd (n + n) =>
"Du kennst ein Lemma um mit `¬odd` umzugehen."

-- Hint (n : ℕ) (k : ℕ) : ¬odd (n + k) =>
-- "Du kennst ein Lemma um mit `¬odd` umzugehen."

Hint (n : ℕ) : even (n + n) =>
"`unfold even` hilft, anzuschauen, was hinter `even` steckt.

Danach musst du wieder mit `use r` ein `(r : ℕ)` angeben, dass du benützen möchtest."

-- Hint (n : ℕ) (k : ℕ) : even (n + k) =>
-- "`unfold even` hilft hier weiter."

Message (n : ℕ) : n + n = 2 * n => "Recap: `ring` löst Gleichungen in `ℕ`."

Conclusion ""

Tactics push_neg intro use rw unfold ring

Lemmas even odd not_even not_odd not_exists not_forall
