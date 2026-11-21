import GameApi

/-!
Test levels whose statement is not a `Prop` but data, e.g. constructing an element of a
type. Inspired by the "Reintroduction to Proofs" game
(https://github.com/emilyriehl/ReintroductionToProofs). Such a statement becomes a `def`
instead of a `theorem`, and is added to the inventory as a definition.
-/

open GameServer Lean Elab Command

Game "TestNonProp"
World "TypeWorld"
Level 1

/-- By pairing any element `a : A` with any element `b : B`, there is an element of `A × B`. -/
Statement pairing {A B : Type} (a : A) (b : B) : A × B := by
  constructor
  Hint (hidden := true) "Now Lean asks you to supply an element of type `{A}`."
  exact a
  Hint (hidden := true) "Now Lean asks you to supply an element of type `{B}`."
  exact b

/-- info: false -/
#guard_msgs in
#eval show CommandElabM Bool from return (← getCurLevel).isProp

/-- info: "def pairing {A B : Type} (a : A) (b : B) : A × B := by" -/
#guard_msgs in
#eval show CommandElabM String from return (← getCurLevel).descrFormat

-- it is a definition which computes
/-- info: (1, "b") -/
#guard_msgs in
#eval pairing 1 "b"

/-- info: true -/
#guard_msgs in
#eval show CommandElabM Bool from do
  return (← getInventoryTemplate? `pairing .Definition).isSome

-- what the client gets: `isProp` and the display name from the definition's documentation
/-- info: (some false, some "pairing") -/
#guard_msgs in
#eval show CommandElabM _ from do
  let info := (← getCurLevel).toInfo (← getEnv)
  return (info.isProp, info.displayName)

Level 2

-- a function type, without a name
Statement {A : Type} : A → A := by
  Hint (hidden := true) "Start with `intro x`."
  intro x
  exact x

/-- info: false -/
#guard_msgs in
#eval show CommandElabM Bool from return (← getCurLevel).isProp

/-- info: "example {A : Type} : A → A := by" -/
#guard_msgs in
#eval show CommandElabM String from return (← getCurLevel).descrFormat

Level 3

-- a `Prop` statement for comparison
Statement {A B : Type} (a : A) (f : A → B) : f a = f a := by
  rfl

/-- info: true -/
#guard_msgs in
#eval show CommandElabM Bool from return (← getCurLevel).isProp
