import Lean

/-!
# Parse doc comments
-/

open Lean Meta Elab Command

namespace GameServer

/-- Read a doc comment and get its content. Return `""` if no doc comment available. -/
def parseDocComment! (doc: Option (TSyntax `Lean.Parser.Command.docComment)) :
    CommandElabM String := do
  match doc with
  | none =>
    logWarning "Add a text to this command with `/-- yada yada -/ MyCommand`!"
    pure ""
  | some s => match s.raw[1] with
    | .atom _ val => pure <| val.dropRight 2 |>.trim
    | _           => pure ""

/-- Read a doc comment and get its content. Return `none` if no doc comment available. -/
def parseDocComment (doc: Option (TSyntax `Lean.Parser.Command.docComment)) :
    CommandElabM <| Option String := do
  match doc with
  | none => pure none
  | some _ => parseDocComment! doc
