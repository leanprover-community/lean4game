import GameApi

open GameServer

#guard isLanguageCode "en"
#guard isLanguageCode "pt-BR"
#guard isLanguageCode "zh-Hans"
#guard isLanguageCode "gsw"
#guard !isLanguageCode "English"
#guard !isLanguageCode "EN"
#guard !isLanguageCode "e"
#guard !isLanguageCode "en-"
#guard !isLanguageCode "en_US"
#guard !isLanguageCode ""

Game "Test"

/-- error: 'English' is not a language code. Use ISO codes like "en" or "pt-BR" instead. -/
#guard_msgs in
Languages "en" "English" "pt-BR"
