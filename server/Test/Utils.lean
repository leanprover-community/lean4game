import GameServer.Utils

/-- info: "hello world,\n \n\nHow are you?\n\n- Fine!" -/
#guard_msgs in
#eval "hello\n       world,\n \n\nHow\n   are\nyou?\n\n- Fine!\n".dropSingleNewlines
