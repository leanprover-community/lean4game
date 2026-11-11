# API

This file lists all endpoints of the server's public API. For the API-interfaces, consult `server/src/api.ts` which is also copied
to `client/src/api.ts`.

| Endpoint                                     | Kind   | Description                                                                                                              |
| -------------------------------------------- | ------ | ------------------------------------------------------------------------------------------------------------------------ |
| `/api/lean/start/:owner/:game`               | POST   | start a new Lean instance for a game                                                                                     |
| `/api/lean/instances/:id`                    | GET    | get information about an existing instance (not used in leangame)                                                        |
| `/api/lean/instances/:id`                    | DELETE | delete the instance. Same as `/api/lean/instances/:id/stop` (not used in leangame)                                       |
| `/api/lean/instances/:id/check`              | POST   | submit a proof to the Lean instance to validate                                                                          |
| `/api/lean/instances/:id/keepalive`          | POST   | keep the instance running. Should be called about once per minute (see `LEAN_IDLE_MINUTES`) if no other request occurred |
| `/api/lean/instances/:id/stop`               | POST   | delete the instance. Same as `DELETE` on `/api/lean/instances/:id`                                                       |
| `/api/lean/instances/count`                  | GET    | number of active instances                                                                                               |
| `/api/import/:owner/:repo/trigger`           | POST   | starts importing a game from Github                                                                                      |
| `/api/import/:owner/:repo`                   | GET    | get the status of the Github-import                                                                                      |
| `/api/load`                                  | GET    | server load: used `memory` and `cpu`, both between 0.0 and 1.0                                                           |
| `/api/games`                                 | GET    | list of visible games                                                                                                    |
| `/api/config`                                | GET    | the public part of the server config: announcements, contact information and legal texts                                 |
| `/api/data/:owner/:game/game`                | GET    | game: game info                                                                                                          |
| `/api/data/:owner/:game/inventory`           | GET    | game: inventory                                                                                                          |
| `/api/data/:owner/:game/level/:world/:level` | GET    | game: level info                                                                                                         |
| `/api/data/:owner/:game/doc/:kind/:name`     | GET    | game: an inventory entry, `:kind` is one of `tactic`, `theorem`, or `definition`                                         |
| `/api/data/:owner/:game/images/*file`        | GET    | game: images, e.g. `images/cover.png`                                                                                    |
| `/api/i18n/:owner/:game/:lang`               | GET    | game: translations                                                                                                       |
