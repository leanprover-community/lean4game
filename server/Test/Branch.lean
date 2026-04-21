import GameServer

/-!
Test that Hints inside a branch are translated.
-/

Game "Test"
World "TestW"
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
