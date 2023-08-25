import GameServer.Commands
--import

Game "Test"
World "TestW"
Level 1

/- Missing doc -/

-- Shows info on `foo.bar`:

/-- some text -/
Statement foo.bar : 5 ≤ 7 := by
  simp

-- Shows warning on `foo.bar₂`:

Statement foo.bar2 : 3 ≤ 7 := by
  simp


NewLemma foo.baz
DisabledTactic tauto


/- Namespace -/

-- test that the command also works inside a namespace
namespace myNamespace

/-- test -/
Statement anotherStatement (n : Nat) : n + 0 = n := by
  rfl

end myNamespace

/- Other tests -/

LemmaDoc add_zero as "add_zero" in "Nat" "(nothing)"

/-- test -/
Statement add_zero (n : Nat) : n + 0 = n := by
  rfl

Statement (n : Nat) : 0 + n = n := by
  Template
    induction n
    Hint ""
    Hole
      simp
    Branch
      skip
      Hint ""
    Hint ""
  simp


NewLemma add_zero

--attribute [simp] add_zero

#print add_zero

theorem xy (n : Nat) : n + 0 = n := by
  simp



/-! Test that it is possible to add `simp` attribute. -/

/-- Doc comment -/
@[simp]
Statement My.add_comm (n m : Nat) : n + m = m + n := by
  rw [Nat.add_comm]

example (n m : Nat) : n + m = m + n := by
  simp

#check My.add_comm
