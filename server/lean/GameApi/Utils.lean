import Lean

namespace GameServer

open Lean Meta Elab Tactic Command

syntax showOptArg := atomic(" (" (&"strict" <|> &"verbose") " := " withoutPosition(term) ")")

instance : Coe String Name where
  coe s := Name.mkSimple s

-- unused
/--
Removes whitespace sequences starting with `\n` which do not contain any
more `\n`. Whitespace sequences which contain multiple `\n` are not modified.
-/
def _root_.String.dropSingleNewlines (s : String) : String := Id.run do
  let mut pos : String.Pos.Raw := 0
  let mut out : String := ""
  while !pos.atEnd s do
    let c := pos.get s
    -- let posₙ := s.next pos
    if c == '\n' then
      let (wsSeq, posₙ) := getWhitespaceSeq s pos
      out := out.append wsSeq
      pos := posₙ
    else
      out := out.push c
      pos := pos.next s
  return String.ofList out.toList
where
  getWhitespaceSeq (s : String) (pos : String.Pos.Raw) : String × String.Pos.Raw := Id.run do
    let mut newLineCount := 0
    let mut pos := pos
    let mut wsSeq := ""
    while !pos.atEnd s && (pos.get s).isWhitespace do
      let c := (pos.get s)
      if c == '\n' then
        newLineCount := newLineCount + 1
      wsSeq := wsSeq.push c
      pos := pos.next s
    match newLineCount, pos.atEnd s with
    | 0, _ => unreachable!
    -- if there is only one `\n` we drop it and return a single space
    | 1, true => return ("", pos)
    | 1, false => return (" ", pos)
    -- multiple consequtive `\n` remain unmodified
    | _, _ => return (wsSeq, pos)
