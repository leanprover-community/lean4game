import GameApi

/-- The way to proof reflexivity. -/
TacticDoc rfl insert "rfl"

/-- To change the goal using equalities. -/
TacticDoc rw insert "rw [$,]"

/-- Can be proven by an existing result. -/
TacticDoc exact

/-- Introduce an auxilary result. -/
TacticDoc «have» insert "have $_ : $+ := by $;"

/-- Assume the premise of an induction. -/
TacticDoc intro

/-- Use an existing result. -/
TacticDoc apply
