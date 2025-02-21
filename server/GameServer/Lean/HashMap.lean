import Lean

def Std.HashMap.merge [BEq α] [Hashable α] (old : Std.HashMap α β) (new : Std.HashMap α β)
  (merge : β → β → β) : Std.HashMap α β :=
new.fold (fun acc a b =>
  if let some bOld := acc.get? a
  then acc.insert a (merge bOld b)
  else acc.insert a b) old
