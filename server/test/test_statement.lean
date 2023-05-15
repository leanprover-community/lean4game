import GameServer.Commands
--import

Game "Test"
World "TestW"
Level 1

/- Missing doc -/

-- Shows warning on `foo.bar`:
Statement foo.bar "some text" : 5 ≤ 7 := by
  simp

NewLemma foo.baz
DisabledTactic tauto

/- Other tests -/

LemmaDoc add_zero as "add_zero" in "Nat" "(nothing)"

Statement add_zero "test" (n : Nat) : n + 0 = n := by
  rfl

Statement (n : Nat) : 0 + n = n := by
  Template
    induction n
    Hole
      simp
    simp

NewLemma add_zero

--attribute [simp] add_zero

#print add_zero

theorem xy (n : Nat) : n + 0 = n := by
  simp
