/- Adapted from `Lean.Parser.StrInterpolation`

This version of interpolated strings deletes any initial spaces from
new lines. This keeps Markdown from interpreting indented material
as quotes.
-/
import Lean
namespace Lean.Parser

/-- Push `(Syntax.node tk <new-atom>)` onto syntax stack if parse was successful. -/
def mkNodeTokenNoWs (n : SyntaxNodeKind) (startPos : String.Pos) : ParserFn := fun c s => Id.run do
  if s.hasError then
    return s
  let input     := c.input
  let stopPos   := s.pos
  let leading   := mkEmptySubstringAt input startPos
  let val       := input.extract startPos stopPos
  let wsStopPos := s.pos
  let trailing  := { str := input, startPos := stopPos, stopPos := wsStopPos : Substring }
  let info      := SourceInfo.original leading startPos trailing stopPos
  s.pushSyntax (Syntax.mkLit n val info)

partial def interpolatedStrNoIndentFn (p : ParserFn) : ParserFn := fun c s =>
  let input     := c.input
  let stackSize := s.stackSize
  let rec parse (startPos : String.Pos) (c : ParserContext) (s : ParserState) : ParserState :=
    let i     := s.pos
    if input.atEnd i then
      let s := s.pushSyntax Syntax.missing
      let s := s.mkNode interpolatedStrKind stackSize
      s.setError "unterminated string literal"
    else
      let curr := input.get i
      let s    := s.setPos (input.next i)
      if curr == '\"' then
        let s := mkNodeToken interpolatedStrLitKind startPos c s
        s.mkNode interpolatedStrKind stackSize
      else if curr == '\n' then
        -- Ignore initial spaces on a new line
        let s := mkNodeTokenNoWs interpolatedStrLitKind startPos c s
        let s := takeWhileFn (fun curr => curr == ' ') c s
        parse s.pos c s
      else if curr == '\\' then
        andthenFn (quotedCharCoreFn isQuotableCharForStrInterpolant) (parse startPos) c s
      else if curr == '{' then
        let s := mkNodeToken interpolatedStrLitKind startPos c s
        let s := p c s
        if s.hasError then s
        else
          let i := s.pos
          let curr := input.get i
          if curr == '}' then
            let s := s.setPos (input.next i)
            parse i c s
          else
            let s := s.pushSyntax Syntax.missing
            let s := s.mkNode interpolatedStrKind stackSize
            s.setError "'}'"
      else
        parse startPos c s
  let startPos := s.pos
  if input.atEnd startPos then
    s.mkEOIError
  else
    let curr  := input.get s.pos;
    if curr != '\"' then
      s.mkError "interpolated string"
    else
      let s := s.next input startPos
      parse startPos c s

@[inline] def interpolatedStrNoIndentNoAntiquot (p : Parser) : Parser := {
  fn   := interpolatedStrNoIndentFn (withoutPosition p).fn,
  info := mkAtomicInfo "interpolatedStrNoIndent"
}

def interpolatedStrNoIndent : Parser :=
  withAntiquot (mkAntiquot "interpolatedStrNoIndent" interpolatedStrKind) $ interpolatedStrNoIndentNoAntiquot termParser

open Lean.PrettyPrinter
open Lean.PrettyPrinter.Parenthesizer
open Lean.PrettyPrinter.Formatter

@[combinator_parenthesizer interpolatedStrNoIndent]
def interpolatedStrNoIndent.parenthesizer := interpolatedStr.parenthesizer

@[combinator_formatter interpolatedStrNoIndent]
def interpolatedStrNoIndent.formatter := interpolatedStr.formatter

end Lean.Parser


/- Adapted from Init/Meta -/
open Lean

private def decodeInterpStrQuotedChar (s : String) (i : String.Pos) : Option (Char × String.Pos) := do
  match Syntax.decodeQuotedChar s i with
  | some r => some r
  | none   =>
    let c := s.get i
    let i := s.next i
    if c == '{' then pure ('{', i)
    else none

private partial def decodeInterpStrLit (s : String) : Option String :=
  let rec loop (i : String.Pos) (acc : String) : Option String :=
    let c := s.get i
    let i := s.next i
    if c == '\"' || c == '{' then
      pure acc
    else if c == '\n' then
      pure (acc.push c)
    else if s.atEnd i then
      pure acc
    else if c == '\\' then do
      let (c, i) ← decodeInterpStrQuotedChar s i
      loop i (acc.push c)
    else
      loop i (acc.push c)
  let c := s.get 0
  if c == '\"' || c == '{' then
    loop ⟨1⟩ ""
  else
    loop ⟨0⟩ ""
partial def isInterpolatedStrLit? (stx : Syntax) : Option String :=
  match Syntax.isLit? interpolatedStrLitKind stx with
  | none     => none
  | some val => decodeInterpStrLit val

open Elab

def expandInterpolatedStrChunks (chunks : Array Syntax) (mkAppend : Syntax → Syntax → TermElabM Syntax) (mkElem : Syntax → TermElabM Syntax) : TermElabM Syntax := do
  let mut i := 0
  let mut result := Syntax.missing
  for elem in chunks do
    let elem ← match isInterpolatedStrLit? elem with
      | none     => mkElem elem
      | some str => mkElem (Syntax.mkStrLit str)
    if i == 0 then
      result := elem
    else
      result ← mkAppend result elem
    i := i+1
  return result

open TSyntax.Compat in
def expandInterpolatedStr (interpStr : TSyntax interpolatedStrKind) (type : Term) (toTypeFn : Term) : TermElabM Term := do
  let r ← expandInterpolatedStrChunks interpStr.raw.getArgs (fun a b => `($a ++ $b)) (fun a => `($toTypeFn $a))
  `(($r : $type))
