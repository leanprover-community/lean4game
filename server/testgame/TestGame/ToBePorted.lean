import Mathlib

lemma not_odd {n : ℕ} : ¬ Odd n ↔ Even n := by sorry

lemma not_even {n : ℕ} : ¬ Even n ↔ Odd n := by sorry

lemma even_square (n : ℕ) : Even n → Even (n ^ 2) := by
  intro ⟨x, hx⟩
  unfold Even at *
  use 2 * x ^ 2
  rw [hx]
  ring

theorem nat_succ (n : ℕ) : Nat.succ n = n + 1 := rfl
