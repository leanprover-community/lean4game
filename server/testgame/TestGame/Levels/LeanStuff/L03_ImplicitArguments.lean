import TestGame.Metadata

import Mathlib
import TestGame.Options.BigOperators

set_option tactic.hygienic false

Game "TestGame"
World "LeanStuff"
Level 3

Title "Implizite Argumente"

Introduction
"

Auch wichtiger Syntax ist der Unterschied zwischen
impliziten und expliziten Argumenten von Lemmas. **Explizite Argumente**
schreibt man mit runden Klammern `()`, **impliziete Argumente** mit geschweiften `{}`.

Als implizit werden alle Argumente markiert, die Lean selbständig aus dem Kontext
erschliessen und einfüllen kann.

Als Beispiel schauen wir uns ein bekanntes Lemma an:
```
lemma Fin.sum_univ_castSucc {β : Type _} [AddCommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) :
    ∑ i : Fin (n + 1), f i = ∑ i : Fin n, f (↑Fin.castSucc.toEmbedding i) + f (Fin.last n) := by
  sorry
```

Hier ist unter anderem `n` als implizites Argument angegeben, da Lean aus `f` herauslesen kann,
was `n` sein muss. Falls man trotzdem einmal das implizites Argument angeben muss
(z.B. um `rw` zu helfen, wenn es mehrere Möglichkeiten gibt),
kann man dies mit `Fin.sum_univ_castSucc (n := m + 1)` machen.
"

open BigOperators

Statement
"Zeige $(\\sum_{i=0}^{m} i) + (m + 1) = \\sum_{i=0}^{m + 1} i$."
    (m : ℕ) :
      ∑ i : Fin (m + 1), (i : ℕ) + (m + 1) = ∑ i : Fin (Nat.succ m + 1), ↑i := by
  rw [Fin.sum_univ_castSucc (n := m + 1)]
  rfl

OnlyTactics rw rfl

NewLemmas Fin.sum_univ_castSucc

HiddenHint (m : ℕ) :
  ∑ i : Fin (m + 1), (i : ℕ) + (m + 1) = ∑ i : Fin (Nat.succ m + 1), ↑i =>
"Das Lemma `Fin.sum_univ_castSucc` hilft."

Hint (m : ℕ) :
  ∑ i : Fin m, (Fin.castSucc.toEmbedding i : ℕ) + ↑(Fin.last m) + (m + 1) =
  ∑ i : Fin (Nat.succ m + 1), ↑i =>
"Hier hat `rw` die falsche der beiden Summen umgeschrieben. Hilf ihm mit
`rw [Fin.sum_univ_castSucc (n := m + 1)]`."

Hint (m : ℕ) :
  ∑ i : Fin (m + 1), (i : ℕ) + (m + 1) =
  ∑ i : Fin (m + 1), ↑i + (m + 1) =>
"Jetzt sind beide Seiten gleich und das Goal kann mit `rfl` geschlossen werden."
