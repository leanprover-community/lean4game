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

Game "Test"
World "TestW"
Level 2 -- should warn if set to `1`

-- Shows warning on `foo.bar₂`:
Statement foo.bar2 : 3 ≤ 7 := by
  simp


NewTheorem foo.bar
DisabledTactic tauto


/- Namespace -/

-- test that the command also works inside a namespace
namespace myNamespace

/-- test -/
Statement anotherStatement (n : Nat) : n + 0 = n := by
  rfl

end myNamespace

/- Other tests -/

TheoremDoc add_zero as "add_zero" in "Nat" "(nothing)"

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


NewTheorem add_zero

--attribute [simp] add_zero

#print add_zero

theorem xy (n : Nat) : n + 0 = n := by
  simp



/-! Test that it is possible to add `simp` attribute. -/

/-- Doc comment -/
@[simp]
Statement My.add_assoc (n m x : Nat) : (m + n) + x = m + (n + x) := by
  rw [Nat.add_assoc]

example (n m : Nat) : (m + n) + x = m + (n + x) := by
  simp

#check My.add_assoc

Statement My.add_comm (preamble := simp [add_comm m n]) (n m : Nat) : n + (m + 0) = m + n := by
  rw [Nat.add_comm]
