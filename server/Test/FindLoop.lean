import GameServer.Helpers
import GameServer.Utils

open GameServer Lean Std

-- E → A → B → C → A and
-- F → G → F
open HashMap in
def testArrows : HashMap Name (HashSet Name) :=
  ofList [("a", (HashSet.emptyWithCapacity.insert "b": HashSet Name).insert "d"),
          ("b", (HashSet.emptyWithCapacity.insert "c": HashSet Name)),
          ("c", (HashSet.emptyWithCapacity.insert "a": HashSet Name)),
          ("d", {}),
          ("f", (HashSet.emptyWithCapacity.insert "g": HashSet Name)),
          ("g", (HashSet.emptyWithCapacity.insert "f": HashSet Name)),
          ("e", (HashSet.emptyWithCapacity.insert "a": HashSet Name).insert "f")]

/-- info: [`a, `b, `c] -/
#guard_msgs in
#eval findLoops testArrows
