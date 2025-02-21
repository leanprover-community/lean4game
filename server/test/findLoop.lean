import GameServer

namespace GameServer

open Lean hiding HashMap HashSet
open Std

-- E → A → B → C → A and
-- F → G → F
open HashMap in
def testArrows : HashMap Name (HashSet Name) :=
  ofList [(`a, (HashSet.empty.insert `b : HashSet Name).insert `d),
          (`b, (HashSet.empty.insert `c : HashSet Name)),
          (`c, (HashSet.empty.insert `a : HashSet Name)),
          (`d, {}),
          (`f, (HashSet.empty.insert `g : HashSet Name)),
          (`g, (HashSet.empty.insert `f : HashSet Name)),
          (`e, (HashSet.empty.insert `a : HashSet Name).insert `f)]

/--
info: [`a, `b, `c]
-/
#guard_msgs in
-- expected: some permutation of ``[`c, `a, `b]`` or ``[`f, `g]``
#eval findLoops testArrows
