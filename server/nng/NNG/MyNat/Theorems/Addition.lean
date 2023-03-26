import NNG.Metadata
import NNG.MyNat.Addition

open MyNat

theorem MyNat.zero_add (n : ℕ) : 0 + n = n := by
  induction n with n hn
  · rw [add_zero]
    rfl
  · rw [add_succ]
    rw [hn]
    rfl

theorem MyNat.add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c)  := by
  induction c with c hc
  · rw [add_zero]
    rw [add_zero]
    rfl
  · rw [add_succ]
    rw [add_succ]
    rw [add_succ]
    rw [hc]
    rfl

theorem MyNat.succ_add (a b : ℕ) : succ a + b = succ (a + b)  := by
  induction b with d hd
  · rw [add_zero]
    rfl
  · rw [add_succ]
    rw [hd]
    rw [add_succ]
    rfl

theorem MyNat.add_comm (a b : ℕ) : a + b = b + a := by
  induction b with d hd
  · rw [zero_add]
    rw [add_zero]
    rfl
  · rw [add_succ]
    rw [hd]
    rw [succ_add]
    rfl

theorem MyNat.one_eq_succ_zero : (1 : ℕ) = succ 0 := by
  rfl
