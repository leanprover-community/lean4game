import GameServer.Commands
--import

Game "Test"
World "TestW"
Level 1

LemmaDoc add_zero as "add_zero" in "Nat" "(nothing)"

@[simp] Statement add_zero "test" (n : Nat) : n + n = n := by
  sorry

Statement (n : Nat) : 0 + n = n := by
  Template
    induction n
    Hole
      simp
    simp

NewLemma add_zero

--attribute [simp] add_zero

#print add_zero

theorem xy (n : Nat) : n + n = n := by
  simp
