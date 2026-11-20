import GameApi.Helpers

/-!
Tests for `GameServer.parseDocCommentD`.

This function parses some raw syntax coming from `lean4` which might
change without warning.
-/

open Lean Elab Command GameServer

elab doc:docComment ? "#parse_doc" : command => do
  logInfo m!"{repr (← parseDocCommentD doc (default := "<default>"))}"

/-! ## `parseDocComment` -/

/-- info: "Hello world" -/
#guard_msgs in
/-- Hello world -/
#parse_doc


/-- info: "last character is included" -/
#guard_msgs in
/--last character is included-/
#parse_doc

/-- info: "Some *markdown* text\n  with `code`" -/
#guard_msgs in
/--
  Some *markdown* text
  with `code`
  -/
#parse_doc

/-- info: "" -/
#guard_msgs in
/---/
#parse_doc

/--
warning: Add a text to this command with `/-- yada yada -/ MyCommand`!
---
info: "<default>"
-/
#guard_msgs in
#parse_doc
