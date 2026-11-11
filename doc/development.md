# Development

It is recommended to use the VSCode Devcontainers: open project in VSCode, the "Ctrl+Shift+P" and select "Dev Containers: Reopen in Container". This lets you develop in a linux environment where all relevant tools are already installed.

## Architecture

The server consists of two parts:

- `server/src`: the Node/Express server. It answers the [API](server/api.md), serves the built client in
  production, imports games from GitHub, and starts a Lean server (`lake serve`)
  in the game's folder to check the proofs (inside a bubblewrap sandbox).
- `server/lean`: the Lean part, a lake package which games depend on. This is also released
  (via `git subtree`) as https://github.com/hhu-adam/gameserver
  - `GameApi` provides the commands to create a game, see the
    [documentation for game creators](game/create_game.md). In particular, `MakeGame`
    compiles the entire game and stores some static information (e.g. Json, images) to `.lake/gamedata`.
    The Node server serves these files under `/api/data`, see [API](server/api.md). The other informations
    are stored in Lean environment extensions, which the Lean process, started with `lake serve`, has access to.
  - `GameServer` is the part of the Lean server which checks the proofs. Most notably, a `check` request writes
    a `Runner` command with all relevant request data into a virtual Lean file to be evaluated
    in the context of the right level of the game.

### Database

The server starts a SQLite database located `server/data/leangame.db` to collect some anonymised and aggregated information
about the usage. This can best be introspected with the "SQLite Viewer" VSCode extension which is preinstalled in
the devcontainer.

It is important that the data stored to the database is anonymised and does not contain any personal data.

### Lean interaction 

Each player starts a Lean instance which they then repeatedly ask through the `check` request. Navigating away will close
the instance.

Currently, for simplicity, each `check` request opens a new RPC-connection for this request, which is afterwards not kept alive
and will be discarded by the Lean server's cleanup. All information, including all possible hover tooltips are precomputed
and included in the response's answer.

There are two future directions one could investigate:

- keeping the RPC alive together with the session and reusing it. This might be neater, but currently the extra bookeeping
  wasn't worth it.
- using one Lean instance for multiple players: This could save a lot of RAM, but one would have to do more bookeeping and
  deal with the potential inference players could have among each other. For example a crash would crash the
  game for all players sharing an instance.

## NPM scripts

- `npm start`: starts the project in development mode, available at `http://localhost:3000`.
  This runs Lean without bubblewrap (see `NODE_ENV`).
- `npm run build`: builds the project for production.
- `npm run prod`: after building, this starts the production server and the client is
  reachable under `http://localhost:8000`.
  Alternatively, `pm2 start ecosystem.config.cjs` does this, too [setup](server/setup.md).
- `npm test`: the Lean tests and the Cypress tests. `npm run test:ui` opens Cypress
  interactively.

To test changes in `server/lean` with a local game, see
[running a game locally](game/running_locally.md#modifying-the-gameserver).

## Updating Lean version

1. make sure `lean-i18n` has been updated
2. edit `server/lean/lean-toolchain` to contain the desired version: `leanprover/lean4:v4.31.0`
3. edit all `require` statements in `server/lean/lakefile.lean` to contain the toolchain (e.g. `"v4.31.0"`) instead of `"main"`
4. call `lake update --keep-toolchain`
5. undo the changes in `server/lean/lakefile.lean`
6. `npm run build:server`
7. on github, create a PR and merge it
8. create a tag, e.g. `v4.31.0`, pointing to the bump commit

## Deploying GameSkeleton and GameServer

_(only relevant for repo maintainers)_

initial setup; add the desired remote once:

```bash
git remote add gameskeleton git@github.com:hhu-adam/GameSkeleton.git
git fetch gameskeleton
git remote add gameserver git@github.com:hhu-adam/GameServer.git
git fetch gameserver
```

Then, the content of `GameSkeleton/` and `server/lean` can be pushed to these repos with

```bash
git subtree push --prefix=GameSkeleton gameskeleton main
git subtree push --prefix=server/lean gameserver main
```

## Pushing Tags

The important tag for the users is the one on `gameserver`.

```
git tag v4.35.0
git push origin v4.35.0
git push gameserver "$(git subtree split --prefix=server/lean v4.35.0)":refs/tags/v4.35.0
```

