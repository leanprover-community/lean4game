import Lake
open Lake DSL

package GameServer

require "leanprover-community" / batteries @ git "v4.31.0"
require "hhu-adam" / i18n @ git "v4.31.0"

-- dev dependency
-- require "leanprover-community" / importGraph @ git "main"

@[default_target]
lean_lib GameServer

@[test_driver]
lean_lib test where
  globs := #[.submodules `Test]
