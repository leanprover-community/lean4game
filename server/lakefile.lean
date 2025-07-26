import Lake
open Lake DSL

package GameServer

-- Using this assumes that each dependency has a tag of the form `v4.X.0`.
def leanVersion : String := s!"v{Lean.versionString}"

require batteries from git "https://github.com/leanprover-community/batteries" @ leanVersion
require i18n from git "https://github.com/hhu-adam/lean-i18n.git" @ leanVersion

require importGraph from git "https://github.com/leanprover-community/import-graph" @ leanVersion

@[default_target]
lean_lib GameServer
