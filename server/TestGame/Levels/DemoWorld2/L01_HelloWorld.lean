import GameServer
import TestGame.Levels.DemoWorld1

World "DemoWorld2"
Level 1

Title "Hello World"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

Statement (h : x = 2) (g : y = 4) : x + x = y := by
  exact demo_statement h g

NewTactic exact

Conclusion "This last message appears if the level is solved."
