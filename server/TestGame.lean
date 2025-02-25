import TestGame.Levels.DemoWorld1
import TestGame.Levels.DemoWorld2

-- Here's what we'll put on the title screen
Title "Test Game"
Introduction
"
This text appears on the starting page where one selects the world/level to play.
You can use markdown.
"

Info "
Here you can put additional information about the game. It is accessible
from the starting through the drop-down menu.

For example: Game version, Credits, Link to Github and Zulip, etc.

Use markdown.
"

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "This game is used for automated tests."
CaptionLong "It can be accessed at `localhost:3000/#/g/test/Test`."
Prerequisites "" -- add this if your game depends on other games

/-- warning: Make sure the cover image 'images/nonexistent.png' exists. -/
#guard_msgs in
CoverImage "images/nonexistent.png"

CoverImage "images/testGameCover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/

MakeGame
