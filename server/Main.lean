import NNG.GameServer.Server
import NNG.NNG

def System.FilePath.parent! (fp : System.FilePath) : System.FilePath :=
  match fp.parent with
  | some path => path
  | none => panic! "Couldn't find parent folder"

unsafe def main : IO Unit := do
  let build_folder := (← IO.appPath).parent!.parent!
  let paths : List System.FilePath := [build_folder/"lib",
                                      (← Lean.findSysroot) / "lib" / "lean"]
  Server.runGame `NNG paths
