import GameServer.Commands

/-!
Test that hints inside a branch are translated.
-/

Game "Test"
World "Test"
Level 1

/--
info: There are 3 keys for tranlation: [level completed! 🎉, level completed with warnings… 🎭, intermediate goal solved! 🎉]
-/
#guard_msgs in
ListTranslations

Statement (n : Nat) : 0 + n = n := by
  Template
    induction n
    Hint "outside"
    Branch
      skip
      Hint "inside"
      simp
    simp
    Hint "outside again"
  simp

/--
info: There are 6 keys for tranlation: [level completed! 🎉,
 level completed with warnings… 🎭,
 intermediate goal solved! 🎉,
 outside,
 inside,
 outside again]
-/
#guard_msgs in
ListTranslations

Level 2

Statement : True := by
  Branch
    Hint "some hint inside branch"
    skip
  trivial

/-- some hint inside branch -/
#guard_msgs (substring := true) in
ListTranslations
