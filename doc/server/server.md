# Server

## Environment variables

List of environment variables which can be used to modify the server. For example, if you use `pm2`, you can set these
in `ecosystem.config.cjs`.

| Name                     | Type                          | Description                                                                                                                                                                                                                    | Default                  |
| ------------------------ | ----------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------------ |
| `NODE_ENV`               | `development` or `production` | `development` is set when started in development mode. It might activate some features only used for development. Most notably, **it disables bubblewrap**!                                                                     | `production`             |
| `NO_BWRAP`               | boolean                       | starts the Lean server without bubblewrap container. You should provide your own sandbox instead to avoid arbitrary user code being run on your machine!                                                                       | `false`                  |
| `PORT`                   | number                        | port of the server                                                                                                                                                                                                             | `8000`                   |
| `HOST`                   | string                        | address where the server listens on, e.g. `127.0.0.1` to only accept connections from a reverse proxy on the same machine                                                                                                      | all addresses            |
| `GAMES_DIR`              | string                        | the path to the folder containing the games, relative from the `server/` folder.                                                                                                                                               | `games`                  |
| `LEAN_MAX_OPEN_DOCS`     | number                        | how many level documents an instance keeps open between checks. Each open document is a separate Lean worker process with the game's imports loaded; the least recently checked document is closed when the limit is exceeded. | `1`                      |
| `LEAN_CHECK_TIMEOUT_MS`  | number                        | maximal duration of a proof check in milliseconds. A check taking longer is answered with `504` and its Lean worker is stopped.                                                                                                | `120000`                 |
| `LEAN_IDLE_MINUTES`      | number                        | an instance without a check or keepalive for this many minutes is stopped                                                                                                                                                      | `5`                      |
| `LEANGAME_GITHUB_TOKEN`  | string                        | GitHub token used to download the artifacts of imported games. Required for imports.                                                                                                                                           | –                        |
| `LEANGAME_GITHUB_USER`   | string                        | user agent sent to GitHub . Required for imports.                                                                                                                                                                              | `leangame`               |
| `GITHUB_API_URL`         | string                        | GitHub API base URL                                                                                                                                                                                                            | `https://api.github.com` |
| `IMPORT_MAX_DOWNLOAD_MB` | number                        | maximal size of a downloaded artifact                                                                                                                                                                                          | `8192`                   |
| `IMPORT_MAX_UNPACKED_MB` | number                        | maximal unpacked size of an artifact                                                                                                                                                                                           | `40960`                  |
| `DATABASE_PATH`          | string                        | path of the SQLite database, relative from the `server/` folder                                                                                                                                                                | `data/leangame.db`       |
| `CONFIG_PATH`            | string                        | path of the config file, relative from the `server/` folder                                                                                                                                                                    | `config.json`            |
| `STATS_IDLE_MINUTES`     | number                        | a gap between two checks longer than this counts as a break in the play statistics, see [statistics](../OLD/stats.md)                                                                                                                 | `20`                     |

## Configuration

The config file `server/config.json` (see `CONFIG_PATH`) contains instance specific configuration. Changes apply without a restart.

Some of the config is served to the client over the API (`/api/config`): `announcements`, `contact`, `impressum`, and `privacy`.
Fields marked as _localised_ are either one string for all
languages or an object like `{ "en": "Germany", "de": "Deutschland" }`, where missing languages fall back to `en`.

| Field               | Type                                         | Description                                                                                           | Default |
| ------------------- | -------------------------------------------- | ----------------------------------------------------------------------------------------------------- | ------- |
| `featuredGames`     | `{ owner: string, repo: string }[]`          | games listed first by `/api/games`, in this order. Featured games which are not imported are skipped. | `[]`    |
| `listImportedGames` | boolean                                      | whether `/api/games` also lists all other imported games.                                             | `false` |
| `announcements`     | `{ title: localised, message: localised }[]` | shown at the top of the landing page, `message` in Markdown                                           | `[]`    |
| `contact`           | object                                       | contact information shown in the impressum and the privacy policy, see below                          | –       |
| `impressum`         | object                                       | further content of the impressum, see below                                                           | –       |
| `privacy`           | object                                       | further content of the privacy policy, see below                                                      | –       |

Subfields:

| Field                    | Type                                | Description                                                          |
| ------------------------ | ----------------------------------- | -------------------------------------------------------------------- |
| `contact.name`           | string                              | the responsible persons                                              |
| `contact.address`        | localised[]                         | address, one entry per line                                          |
| `contact.phone`          | string                              | phone number                                                         |
| `contact.url`            | string                              | link to further contact details                                      |
| `contact.technicalEmail` | string                              | email address for technical questions                                |
| `impressum.legalForm`    | localised                           | legal form, representation and supervisory authority of the operator |
| `impressum.vatId`        | string                              | VAT identification number (according to §27a UStG)                   |
| `impressum.link`         | `{ label: localised, url: string }` | link to the impressum of the operating institution                   |
| `privacy.serverLocation` | localised                           | country where the server is located                                  |
