import Lean.Environment
import Lean.Server.Watchdog

namespace GameServer

open Lean

structure GameServerState where
  env : Lean.Environment
  game : Name
  gameDir : String
  inventory : Array String
  difficulty : Nat

abbrev GameServerM := StateT GameServerState Server.Watchdog.ServerM

instance : MonadEnv GameServerM := {
  getEnv := do return (← get).env
  modifyEnv := fun f => do
    let s ← get
    set {s with env := f s.env}
}
