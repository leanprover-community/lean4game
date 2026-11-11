import GameApi.EnvExtensions
import I18n

/-!
Commands to specify the current game/world/level and define auxilary information
like introduction or conclusion of the game/world/level
-/

namespace GameServer

open Lean

/-- Switch to the specified `Game` (and create it if non-existent). Example: `Game "NNG"` -/
elab "Game" n:str : command => do
  let name := n.getString
  setCurGameId name
  if (← getGame? name).isNone then
    insertGame name {name}

/-- Create a new world in the active game. Example: `World "Addition"` -/
elab "World" n:str : command => do
  let name := n.getString
  setCurWorldId name
  if ¬ (← getCurGame).worlds.nodes.contains name then
    addWorld {name}

/-- Define the current level number. Levels inside a world must be
numbered consecutive starting with `1`. Example: `Level 1` -/
elab "Level" level:num : command => do
  let level := level.getNat
  setCurLevelIdx level
  addLevel {index := level}

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
