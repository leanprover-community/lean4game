import GameServer.Layer.Extension
import I18n

namespace GameServer

open Lean Elab

/-- Define the title of the current game/world/level. -/
elab "Title" t:str : command => do
  let title ← t.getString.translate
  match ← getCurLayer with
  | .Level => modifyCurLevel fun level => pure {level with title := title}
  | .World => modifyCurWorld  fun world => pure {world with title := title}
  | .Game => modifyCurGame  fun game => pure {game with
      title := title
      tile := {game.tile with title := title}}

/-- Define the introduction of the current game/world/level. -/
elab "Introduction" t:str : command => do
  let intro ← t.getString.translate
  match ← getCurLayer with
  | .Level => modifyCurLevel fun level => pure {level with introduction := intro}
  | .World => modifyCurWorld  fun world => pure {world with introduction := intro}
  | .Game => modifyCurGame  fun game => pure {game with introduction := intro}

/-- Provide the location of the image for the current game/world/level.
Paths are relative to the lean project's root. -/
elab "Image" t:str : command => do
  let file := t.getString
  if not <| ← System.FilePath.pathExists file then
    logWarningAt t s!"Make sure the cover image '{file}' exists."
  if not <| file.startsWith "images/" then
    logWarningAt t s!"The file name should start with `images/`. Make sure all images are in that folder."

  match ← getCurLayer with
  | .Level =>
    logWarning "Level-images not implemented yet" -- TODO
    modifyCurLevel fun level => pure {level with image := file}
  | .World =>
    modifyCurWorld  fun world => pure {world with image := file}
  | .Game =>
    logWarning "Main image of the game not implemented yet" -- TODO
    modifyCurGame  fun game => pure {game with image := file}

/-- Define the conclusion of the current game or current level if some
building a level. -/
elab "Conclusion" t:str : command => do
  let conclusion ← t.getString.translate
  match ← getCurLayer with
  | .Level => modifyCurLevel fun level => pure {level with conclusion := conclusion}
  | .World => modifyCurWorld  fun world => pure {world with conclusion := conclusion}
  | .Game => modifyCurGame  fun game => pure {game with conclusion := conclusion}

/-!
# Game Info

The following commands provide information about the game which is used on the landing
page and in the menu (e.g. credits).
-/

/-- Define the info of the current game. Used for e.g. credits -/
elab "Info" t:str : command => do
  let info ← t.getString.translate
  match ← getCurLayer with
  | .Level =>
    logError "Can't use `Info` in a level!"
    pure ()
  | .World =>
    logError "Can't use `Info` in a world"
    pure ()
  | .Game => modifyCurGame  fun game => pure {game with info := info}

/-- A list of games that should be played before this one. Example `Prerequisites "NNG" "STG"`. -/
elab "Prerequisites" t:str* : command => do
  modifyCurGame fun game => pure {game with
    tile := {game.tile with prerequisites := t.map (·.getString) |>.toList}}

/-- Short caption for the game (1 sentence) -/
elab "CaptionShort" t:str : command => do
  let caption ← t.getString.translate
  modifyCurGame fun game => pure {game with
    tile := {game.tile with short := caption}}

/-- More detailed description what the game is about (2-4 sentences). -/
elab "CaptionLong" t:str : command => do
  let caption ← t.getString.translate
  modifyCurGame fun game => pure {game with
    tile := {game.tile with long := caption}}

/-- A list of Languages the game is translated to. For example `Languages "de" "en"`.

The keys are ISO language codes.
 -/
elab "Languages" t:str* : command => do
  modifyCurGame fun game => pure {game with
    tile := {game.tile with languages := t.map (·.getString) |>.toList}}

/-- The Image of the game (optional). TODO: Not implemented -/
elab "CoverImage" t:str : command => do
  let file := t.getString
  if not <| ← System.FilePath.pathExists file then
    logWarningAt t s!"Make sure the cover image '{file}' exists."
  if not <| file.startsWith "images/" then
    logWarningAt t s!"The file name should start with `images/`. Make sure all images are in that folder."

  modifyCurGame fun game => pure {game with
    tile := {game.tile with image := file}}
