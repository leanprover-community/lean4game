# Statistics

The server keeps track of a few anonymous usage statistics using an SQLite database located
under `server/data/leangame.db` (or `DATABASE_PATH`).

| Endpoint         | Kind | Description                                                                                                                                                      |
| ---------------- | ---- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `/stats/imports` | GET  | import statistics of all imported games                                                                                                                          |
| `/stats/games`   | GET  | play statistics per game, language and 30-minute interval. Optional query parameters `from` and `to` (e.g. `2026-10-22`) restrict the intervals to `[from, to)`. |
