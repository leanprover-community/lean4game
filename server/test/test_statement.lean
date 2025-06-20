import GameServer
--import

Game "Test"
World "TestW"
Level 1

/- Missing doc -/

-- Shows info on `foo.bar`:

/--
info: Missing Theorem Documentation: foo.bar, used default (e.g. provided docstring) instead. If you want to write a different description, add `TheoremDoc foo.bar` somewhere above this statement.
-/
#guard_msgs in

/-- some text -/
Statement foo.bar : 5 ≤ 7 := by
  simp

Game "Test"
World "TestW"
Level 2 -- should warn if set to `1`

/--
warning: Missing Theorem Documentation: foo.bar2
Add `TheoremDoc foo.bar2` somewhere above this statement.
-/
#guard_msgs in

-- Shows warning on `foo.bar₂`:
Statement foo.bar2 : 3 ≤ 7 := by
  simp


NewTheorem foo.bar

/--
warning: Could not find a docstring for tactic tauto, consider adding one using `TacticDoc tauto "some doc"`
---
warning: Missing Tactic Documentation: tauto
Add `TacticDoc tauto` somewhere above this statement.
-/
#guard_msgs in

DisabledTactic tauto


/- Namespace -/

-- test that the command also works inside a namespace
namespace myNamespace

/--
info: Missing Theorem Documentation: myNamespace.anotherStatement, used default (e.g. provided docstring) instead. If you want to write a different description, add `TheoremDoc myNamespace.anotherStatement` somewhere above this statement.
-/
#guard_msgs in

/-- test -/
Statement anotherStatement (n : Nat) : n + 0 = n := by
  rfl

end myNamespace

/- Other tests -/

/--
warning: You should use the new Syntax:

      /-- yada yada -/
      YourCommand

      instead of

      YourCommand "yada yada"
-/
#guard_msgs in

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


/--
warning: You should only use one `NewTheorem` per level, but it can take multiple arguments: `{cmd} obj₁ obj₂ obj₃`!
-/
#guard_msgs in

NewTheorem add_zero

--attribute [simp] add_zero

/--
info: theorem add_zero : ∀ (n : Nat), n + 0 = n :=
fun n => Eq.refl (n + 0)
-/
#guard_msgs in

#print add_zero

theorem xy (n : Nat) : n + 0 = n := by
  simp



/-! Test that it is possible to add `simp` attribute. -/

/--
info: Missing Theorem Documentation: My.add_assoc, used default (e.g. provided docstring) instead. If you want to write a different description, add `TheoremDoc My.add_assoc` somewhere above this statement.
-/
#guard_msgs in

/-- Doc comment -/
@[simp]
Statement My.add_assoc (n m x : Nat) : (m + n) + x = m + (n + x) := by
  rw [Nat.add_assoc]

example (n m : Nat) : (m + n) + x = m + (n + x) := by
  simp

/-- info: My.add_assoc (n m x : Nat) : m + n + x = m + (n + x) -/
#guard_msgs in

#check My.add_assoc

/--
warning: Missing Theorem Documentation: My.add_comm
Add `TheoremDoc My.add_comm` somewhere above this statement.
-/
#guard_msgs in

Statement My.add_comm (preamble := simp [add_comm m n]) (n m : Nat) : n + (m + 0) = m + n := by
  rw [Nat.add_comm]
