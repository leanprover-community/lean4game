import Game.Levels.HelloWorld

Title "Game Skeleton"
Introduction
"
This is the introduction text of the game.
"

Conclusion
"
This conclusion is shown on the game overview once all worlds are completed.
"

Info "
Here you can put additional information about the game. It is accessible
from the starting through the drop-down menu.

For example: Game version, Credits, Link to Github and Zulip, etc.

Use **markdown**.
"

Languages "en" "de"
CaptionShort "A small template game."
CaptionLong "You should use this game as a template for your own game and add your own levels. `lean`"
-- Prerequisites "NNG4" -- add this if your game builds on other games
CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
