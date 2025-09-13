import Lake
open Lake DSL

package GameServer

-- Using this assumes that each dependency has a tag of the form `v4.X.0`.
def leanVersion : String := s!"v{Lean.versionString}"

require "leanprover-community" / batteries @ git leanVersion
require "hhu-adam" / i18n @ git "main" -- TMP

-- dev dependency
require importGraph from git "https://github.com/leanprover-community/import-graph" @ leanVersion

@[default_target]
lean_lib GameServer

@[test_driver]
lean_lib test
