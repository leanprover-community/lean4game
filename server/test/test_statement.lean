import GameServer.Commands

Game "Test"
World "TestW"
Level 1

LemmaDoc add_zero as "add_zero" in "Nat" "(nothing)"

Statement add_zero (attr := simp, to_additive) "test" (n : Nat) : n + 0 = n := by
  rfl
