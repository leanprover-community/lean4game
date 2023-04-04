import Adam.Options.MathlibPart

open BigOperators

lemma arithmetic_sum (n : ℕ) : 2 * (∑ i : Fin (n + 1), ↑i) = n * (n + 1) := by
  induction' n with n hn
  simp
  rw [Fin.sum_univ_castSucc]
  rw [mul_add]
  simp
  rw [mul_add, hn]
  simp_rw [Nat.succ_eq_one_add]
  ring
