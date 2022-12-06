import Mathlib

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
