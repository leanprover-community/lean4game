import Adam.Metadata


Game "Adam"
World "Numbers"
Level 2

Title ""

Introduction
"
  Das Lemma, das du gerade bewiesen hast, findest du als `pnat.ne_zero`
"

Statement
""
    (a b : ℕ+) : (a : ℕ) * b ≠ 0 := by
  by_contra h
  rw [Nat.mul_eq_zero] at h
  cases h
  have := PNat.ne_zero a
  contradiction
  have := PNat.ne_zero b
  contradiction
