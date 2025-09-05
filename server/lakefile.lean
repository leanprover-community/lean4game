import Lake
open Lake DSL

package GameServer

-- Using this assumes that each dependency has a tag of the form `v4.X.0`.
def leanVersion : String := s!"v{Lean.versionString}"

require "leanprover-community" / batteries @ git "a67fc66cd1ebc0855dc064a4be727798771c0f89" -- TODO: leanVersion
require "hhu-adam" / i18n -- TODO: @ git leanVersion

require "leanprover-community" / importGraph -- TODO: @ git leanVersion

@[default_target]
lean_lib GameServer

@[test_driver]
lean_lib test
