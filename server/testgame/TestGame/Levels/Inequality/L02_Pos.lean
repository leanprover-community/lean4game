import TestGame.Metadata

import Mathlib.Tactic.LibrarySearch

set_option tactic.hygienic false

Game "TestGame"
World "Inequality"
Level 2

Title "Kleinergleich"

Introduction
"
Es gibt zwei intrinsische Möglichkeiten, zu sagen dass `(n : ℕ)` nicht Null ist:
`n ≠ 0` oder `0 < n`.

Das folgende Lemma kannst du immer brauchen um zwischen den beiden zu wechseln.

(*Note:* `0 < n` wird in Lemma-Namen oft mit `_pos` beschrieben anstatt `zero_lt`, siehe z.B.
`Nat.succ_pos`.)


"

Statement Nat.pos_iff_ne_zero
"Benutze Induktion um zu zeigen, dass $0 < n$ und $n \\ne 0$ äquivalent sind."
    (n : ℕ) : 0 < n ↔ n ≠ 0 := by
  induction n
  simp
  constructor
  intro
  simp
  intro
  apply Nat.succ_pos

NewTactic simp
NewLemma Nat.succ_pos

Hint : 0 < Nat.zero ↔ Nat.zero ≠ 0 =>
"Den Induktionsanfang kannst du oft mit `simp` lösen."

Hint (n : ℕ) (h : 0 < n ↔ n ≠ 0) : 0 < Nat.succ n ↔ Nat.succ n ≠ 0 =>
"Jetzt der Induktionsschritt. Fang mal mit `constructor` an."

HiddenHint (n : ℕ) : 0 < Nat.succ n → Nat.succ n ≠ 0 =>
"Auch das kann `simp`."

Hint (n : ℕ) : n.succ ≠ 0 =>
"Auch das kann `simp`."

Hint (n : ℕ) : 0 < Nat.succ n =>
"Hier kannst du das Lemma `Nat.succ_pos` mit `apply` anwenden."



/- Second, less ideal path -/

Hint (n : ℕ) (h : 0 < n) : n ≠ 0 =>
"An dieser Stelle fürst du am besten einen Beweis durch Widerspruch."

HiddenHint (n : ℕ) (h : 0 < n) : n ≠ 0 =>
"Das macht man mit `by_contra`."

Hint (n : ℕ) (h : 0 < n) (g : n = 0) : False =>
"Brauche `rw [_] at _` um eine Annahme `0 < 0` zu erzeugen."

HiddenHint (h : 0 < 0) : False =>
"Mit `contradiction` schliesst du den Widerspruchsbeweis."

Hint (n : ℕ) (h : n ≠ 0) : 0 < n =>
"Diese Richtung beweist du am besten per Induktion."

HiddenHint (n : ℕ) (h : n ≠ 0) : 0 < n =>
"Starte mit `induction n`."

 HiddenHint : 0 < Nat.zero =>
"Mit `contradiction` kannst du den Induktionsanfang schliessen."
