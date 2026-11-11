# Development

## Architecture

The server consists of two parts:

- `server/src`: the Node server. It answers the [API](server/api.md), serves the built client in
  production, imports games from GitHub, and starts a Lean server (`lake serve`) per player
  in the game's folder to check the proofs, inside a bubblewrap sandbox.
- `server/lean`: the Lean part, a lake package which games depend on. This is also released
  as git subtree under https://github.com/hhu-adam/gameserver
  - `GameApi` provides the commands to create a game, see the
    [documentation for game creators](game/create_game.md). In particular, `MakeGame`
    compiles the entire game: static information is stored as JSON files in
    `.lake/gamedata`, which the Node server serves, other data is only saved to Lean
    environment extensions.
  - `GameServer` is the part of the Lean server which checks the proofs.

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

## Deploying GameSkeleton and GameServer

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

## Updating Lean version

1. make sure `lean-i18n` has been updated
2. edit `server/lean/lean-toolchain` to contain the desired version: `leanprover/lean4:v4.31.0`
3. edit all `require` statements in `server/lean/lakefile.lean` to contain the toolchain (e.g. `"v4.31.0"`) instead of `"main"`
4. call `lake update --keep-toolchain`
5. undo the changes in `server/lean/lakefile.lean`
6. `npm run build:server`
7. on github, create a PR and merge it
8. create a tag, e.g. `v4.31.0`, pointing to the bump commit
