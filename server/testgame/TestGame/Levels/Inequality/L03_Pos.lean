import TestGame.Metadata

Game "TestGame"
World "Inequality"
Level 3

Title "Kleinergleich"

Introduction
"
Es gibt zwei intrinsische Möglichkeiten, zu sagen dass `(n : ℕ)` nicht Null ist:
`n ≠ 0` oder `0 < n`.

Das folgende Lemma kannst du immer brauchen um zwischen den beiden zu wechseln.

Note: `0 < n` wird in Lemmanamen oft mit `_pos` beschrieben anstatt `zero_lt`, siehe z.B.
`Nat.succ_pos`.
"

Statement zero_lt_iff
"$0 < n$ und $n \\ne 0$ sind äquivalente Aussagen."
    (n : ℕ) : 0 < n ↔ n ≠ 0 := by
  constructor
  intro h
  by_contra g
  rw [g] at h
  contradiction
  intro h
  induction n
  contradiction
  apply Nat.succ_pos

NewLemmas Nat.succ_pos

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

Hint (m : ℕ) : 0 < Nat.succ m =>
"Hier kannst du das Lemma `Nat.succ_pos` anwenden."
