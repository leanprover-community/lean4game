import Lean

namespace GameServer

open Lean Meta Elab Tactic Command

syntax showOptArg := atomic(" (" (&"strict" <|> &"verbose") " := " withoutPosition(term) ")")

instance : Coe String Name where
  coe s := Name.mkSimple s

/--
Lists all available options that can be used with `set_option`.

Use `set_option (verbose := true)` to display more than just the option names.
The form `#show_option id` will show only options that begin with `id`.

Copied from `#help option` from mathlib.
-/
elab "#show_option" verbose:(ppSpace showOptArg)? id:(ppSpace Parser.rawIdent)? : command => do
  let id := id.map (·.raw.getId.toString false)
  let mut decls : Lean.RBMap _ _ compare := {}
  for (name, decl) in show Lean.RBMap .. from ← getOptionDecls do
    let name := name.toString false
    if let some id := id then
      if !id.isPrefixOf name then
        continue
    decls := decls.insert name decl
  let mut msg := Format.nil
  let opts ← getOptions
  if decls.isEmpty then
    match id with
    | some id => throwError "no options start with {id}"
    | none => throwError "no options found (!)"
  for (name, decl) in decls do
    let mut msg1 := match decl.defValue with
    | .ofString val => s!"String := {repr val}"
    | .ofBool val => s!"Bool := {repr val}"
    | .ofName val => s!"Name := {repr val}"
    | .ofNat val => s!"Nat := {repr val}"
    | .ofInt val => s!"Int := {repr val}"
    | .ofSyntax val => s!"Syntax := {repr val}"
    if let some val := opts.find name then
      msg1 := s!"{msg1}  (currently: {val})"
    msg := match verbose with
    | some opt =>
      match opt with
      | `(showOptArg| (verbose := true)) =>
        msg ++ .nest 2 (f!"option {name} : {msg1}" ++ .line ++ decl.descr) ++ .line ++ .line
      | _ =>
        msg ++ (f!"{name}" ++ .line )
    | none =>
      msg ++ (f!"{name}" ++ .line )

  logInfo msg
