import TestGame.Metadata

import Mathlib
import TestGame.Options.BigOperators

set_option tactic.hygienic false

Game "TestGame"
World "LeanStuff"
Level 4

Title "Instanz-Argumente"

Introduction
"
Bezüglich impliziten Argumente gibt es noch einige weitere Punkte oder Tricks,
die man wissen sollte.

* Instanz-Argumente wie `[Ring R]` sind auch impilzite Argumente. Der Unterschied ist, dass
  Lean einen anderen Mechanismus braucht, um diese zu füllen: Es sucht nach einer entsprechenden
  *Instanz* und, setzt die erste solche Instanz ein.
  Ausserhalb eines Beweises könnte man auch mit
  ```
  #synth Ring ℤ
  ```
  testen, ob Lean eine ensprechende Instanz findet. Instanzen werden dafür gebraucht, Typen
  mit (algebraischer) Stukturen zu versehen.
* Ein `_` irgendwo im Lean-Code ist immer ein Platzhalter, den Lean versucht aus dem Kontext zu
  füllen. Das kann praktisch sein, wenn man etwas nicht ausschreiben will, das offensichtlich ist.
* Mit `@` kann man forcieren, dass alle Argumente explizit sind.
  Für ein Lemma
  ```
  lemma not_or_of_imp {A B : Prop} (h : A → B) :
      ¬A ∨ B := sorry
  ```
  heisst das zum Beispiel dass `not_or_of_imp g` das gleiche ist wie
  `@not_or_of_imp _ _ g`.

  Und `Fin.sum_univ_castSucc (n := m + 1)` könnte man auch als
  `@Fin.sum_univ_castSucc _ _ (m + 1)` schreiben.
"

open BigOperators

Statement
"Zeige $(\\sum_{i=0}^{m} i) + (m + 1) = \\sum_{i=0}^{m + 1} i$."
    (m : ℕ) :
      ∑ i : Fin (m + 1), (i : ℕ) + (m + 1) = ∑ i : Fin (Nat.succ m + 1), ↑i := by
  rw [Fin.sum_univ_castSucc (n := m + 1)]
  rfl

OnlyTactic rw rfl

NewLemma Fin.sum_univ_castSucc

Hint (m : ℕ) :
  ∑ i : Fin (m + 1), (i : ℕ) + (m + 1) = ∑ i : Fin (Nat.succ m + 1), ↑i =>
"
  Probier nochmals das gleiche, diesmal mit
```
rw [@Fin.sum_univ_castSucc _ _ (m + 1)]
```
anstatt
```
rw [Fin.sum_univ_castSucc (n := m + 1)]
```
"

Hint (m : ℕ) :
  ∑ i : Fin m, (Fin.castSucc.toEmbedding i : ℕ) + ↑(Fin.last m) + (m + 1) =
  ∑ i : Fin (Nat.succ m + 1), ↑i =>
"Sackgasse!"


Hint (m : ℕ) :
  ∑ i : Fin (m + 1), (i : ℕ) + (m + 1) =
  ∑ i : Fin (m + 1), ↑i + (m + 1) =>
"Jetzt sind beide Seiten gleich und das Goal kann mit `rfl` geschlossen werden."
