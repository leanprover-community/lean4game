import GameApi

open GameServer Lean

Game "TestTacticInsert"

/-- doc -/
TacticDoc rw insert "rw [$,]"

/-- doc -/
TacticDoc apply in "Basics" insert "apply $_ at $+"

/-- doc -/
TacticDoc exact

/-- doc -/
TacticDoc «have»

/-- the template of a tactic, or `"missing"` -/
def tacticInsert (name : Name) : Elab.Command.CommandElabM String := do
  let some template ← getInventoryTemplate? name .Tactic | return "missing"
  return template.insert.getD "none"

/-- info: "rw [$,]" -/
#guard_msgs in
#eval tacticInsert `rw

/-- info: "apply $_ at $+" -/
#guard_msgs in
#eval tacticInsert `apply

-- the default
/-- info: "exact $+" -/
#guard_msgs in
#eval tacticInsert `exact

-- without the escaping of the identifier
/-- info: "have $+" -/
#guard_msgs in
#eval tacticInsert `«have»

-- `insert` is not a keyword, so it is still an identifier
example (insert : Nat) : Nat := insert
