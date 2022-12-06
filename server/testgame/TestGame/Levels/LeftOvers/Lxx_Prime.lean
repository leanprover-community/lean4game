import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

-- TODO: `even`/`odd` sind in Algebra.Parity. Not ported yet
def even (a : ℕ) : Prop := ∃ r, a = 2 * r
def odd (a : ℕ) : Prop := ∃ k, a = 2 * k + 1

lemma not_odd {n : ℕ} : ¬ odd n ↔ even n := by sorry

lemma not_even {n : ℕ} : ¬ even n ↔ odd n := by sorry

lemma even_square (n : ℕ) : even n → even (n ^ 2) := by
  intro ⟨x, hx⟩
  unfold even at *
  use 2 * x ^ 2
  rw [hx]
  ring

def prime (n : ℕ) : Prop := (2 ≤ n) ∧ ∀ a b, n = a * b → a = 1 ∨ b = 1

Game "TestGame"
World "Nat"
Level 4

Title "Für alle"

Introduction
"
Eine Primzahl könnte man folgendermassen implementieren:
```
def prime (p : ℕ) : Prop := (2 ≤ p) ∧ (∀ a b, p = a * b → a = 1 ∨ b = 1)
```
Also, eine Zahl `p` ungleich `0` oder `1`, für die gilt wenn `a * b = p` dann ist
entweder `a` oder `b` eins.

(Tatsächlich ist eine Primzahl dann etwas genereller definiert, aber dazu mehr später.)




"

Statement
  "Wenn `n * m` eine Primzahl ist, dann ist einer der beiden Faktoren eins."
  (p n m : ℕ) (h : prime p) (h₂ : p = m * n) : n = 1 ∨ m = 1 := by
  unfold prime at h
  rcases h with ⟨l, r⟩
  apply r
  rw [h₂]
  ring



Message (n : ℕ) (hn : odd n) (h : ∀ (x : ℕ), (odd x) → even (x + 1)) : even (n + 1) =>
"`∀ (x : ℕ), (odd x) → even (x + 1)` ist eigentlich das gleiche wie
`(x : ℕ) → `"

Tactics ring intro unfold
