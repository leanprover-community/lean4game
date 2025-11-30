import Lake
open Lake DSL

package GameServer

-- Using this assumes that each dependency has a tag of the form `v4.X.0`.
def leanVersion : String := s!"v{Lean.versionString}"

require "leanprover-community" / batteries @ git "v4.24.0"
require "hhu-adam" / i18n @ git leanVersion

-- dev dependency
require "leanprover-community" / importGraph @ git "v4.24.0"

@[default_target]
lean_lib GameServer

@[test_driver]
lean_lib test where
  globs := #[.submodules `Test]
