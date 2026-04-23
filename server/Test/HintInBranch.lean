import GameServer.Commands

Game "Test"
World "Test"
Level 1

Statement : True := by
  Branch
    Hint "some hint inside branch"
    skip
  trivial

/-- some hint inside branch -/
#guard_msgs (substring := true) in
ListTranslations
