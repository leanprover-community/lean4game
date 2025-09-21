import Lean

namespace GameServer

open Lean Meta Elab Tactic Command

syntax showOptArg := atomic(" (" (&"strict" <|> &"verbose") " := " withoutPosition(term) ")")

instance : Coe String Name where
  coe s := Name.mkSimple s

-- TODO
-- /--
-- Lists all available options that can be used with `set_option`.

-- Use `set_option (verbose := true)` to display more than just the option names.
-- The form `#show_option id` will show only options that begin with `id`.

-- Copied from `#help option` from mathlib.
-- -/
-- elab "#show_option" verbose:(ppSpace showOptArg)? id:(ppSpace Parser.rawIdent)? : command => do
--   let id := id.map (·.raw.getId.toString false)
--   let mut decls : Lean.RBMap _ _ compare := {}
--   for (name, decl) in show Lean.RBMap .. from ← getOptionDecls do
--     let name := name.toString false
--     if let some id := id then
--       if !id.isPrefixOf name then
--         continue
--     decls := decls.insert name decl
--   let mut msg := Format.nil
--   let opts ← getOptions
--   if decls.isEmpty then
--     match id with
--     | some id => throwError "no options start with {id}"
--     | none => throwError "no options found (!)"
--   for (name, decl) in decls do
--     let mut msg1 := match decl.defValue with
--     | .ofString val => s!"String := {repr val}"
--     | .ofBool val => s!"Bool := {repr val}"
--     | .ofName val => s!"Name := {repr val}"
--     | .ofNat val => s!"Nat := {repr val}"
--     | .ofInt val => s!"Int := {repr val}"
--     | .ofSyntax val => s!"Syntax := {repr val}"
--     if let some val := opts.find name then
--       msg1 := s!"{msg1}  (currently: {val})"
--     msg := match verbose with
--     | some opt =>
--       match opt with
--       | `(showOptArg| (verbose := true)) =>
--         msg ++ .nest 2 (f!"option {name} : {msg1}" ++ .line ++ decl.descr) ++ .line ++ .line
--       | _ =>
--         msg ++ (f!"{name}" ++ .line )
--     | none =>
--       msg ++ (f!"{name}" ++ .line )

--   logInfo msg

-- unused
/--
Removes whitespace sequences starting with `\n` which do not contain any
more `\n`. Whitespace sequences which contain multiple `\n` are not modified.
-/
def _root_.String.dropSingleNewlines (s : String) : String := Id.run do
  let mut pos : String.Pos := 0
  let mut out : String := ""
  while !s.atEnd pos do
    let c := s.get pos
    -- let posₙ := s.next pos
    if c == '\n' then
      let (wsSeq, posₙ) := getWhitespaceSeq s pos
      out := out.append wsSeq
      pos := posₙ
    else
      out := out.push c
      pos := s.next pos
  return ⟨out.toList⟩
where
  getWhitespaceSeq (s : String) (pos : String.Pos) : String × String.Pos := Id.run do
    let mut newLineCount := 0
    let mut pos := pos
    let mut wsSeq := ""
    while !s.atEnd pos && (s.get pos).isWhitespace do
      let c := (s.get pos)
      if c == '\n' then
        newLineCount := newLineCount + 1
      wsSeq := wsSeq.push c
      pos := s.next pos
    match newLineCount, s.atEnd pos with
    | 0, _ => unreachable!
    -- if there is only one `\n` we drop it and return a single space
    | 1, true => return ("", pos)
    | 1, false => return (" ", pos)
    -- multiple consequtive `\n` remain unmodified
    | _, _ => return (wsSeq, pos)
