import Lean

/-! This document contains custom options available in the game. -/

/-- Let `MakeGame` print the reasons why the worlds depend on each other. -/
register_option lean4game.showDependencyReasons : Bool := {
  defValue := false
  descr := "show reasons for calculated world dependencies."
}

/-- Let `MakeGame` print the reasons why the worlds depend on each other.

Note: currently unused in favour of setting `set_option trace.debug true`. -/
register_option lean4game.verbose : Bool := {
  defValue := false
  descr := "display more info messages to help developing the game."
}
