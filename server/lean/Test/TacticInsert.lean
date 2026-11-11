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

/-- doc -/
TheoremDoc Nat.add_comm as "add_comm" in "Nat" insert "add_comm"

/-- doc -/
TheoremDoc Nat.succ_pos as "succ_pos"

/-- doc -/
DefinitionDoc HAdd.hAdd as "+" insert "+"

/-- doc -/
DefinitionDoc Nat as "ℕ"

/-- the insertion of a theorem or definition, `"none"` for the default -/
def itemInsert (name : Name) (type : InventoryType) : Elab.Command.CommandElabM String := do
  let some template ← getInventoryTemplate? name type | return "missing"
  return template.insert.getD "none"

/-- info: "add_comm" -/
#guard_msgs in
#eval itemInsert `Nat.add_comm .Theorem

/-- info: "none" -/
#guard_msgs in
#eval itemInsert `Nat.succ_pos .Theorem

/-- info: "+" -/
#guard_msgs in
#eval itemInsert `HAdd.hAdd .Definition

/-- info: "none" -/
#guard_msgs in
#eval itemInsert `Nat .Definition
