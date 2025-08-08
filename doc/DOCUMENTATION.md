# Server

The server is made out of two parts, named "relay" and "server".

The former, "relay", is the server which
sets up a socket connection to the client, starts the lean servers to work on files and
relays messages between the lean server and the client. `index.mjs` is the file that needs to
be run, which is done for example using `pm2` or by calling `npm run start_server` or
`npm run production`, see more later.

The latter, "server", is the lean server which has two jobs. For one, it produces the "gameserver"
executable which is the lean server that handles the files the player plays on. The second job
is to provide the lean commands which are used when creating a game. These are located in
`Commands.lean`.


## Integration into Games

Games need the "server" as a lake-dependency, which is done in the game's lakefile.

A game imports `GameServer` which provides to all the API required to
create a game.

In particular the lean command `MakeGame` compiles the entire game. Static information is
stored as JSON files in `.lake/gamedata` for faster loading, while other data is only
saved to lean env-extensions which the lean server has access to after loading the lean file.

For games to be run successfully, it is important that the "gameserver" executable inside
the game's `.lake` folder is actually built.
Currently, this happens through a lake-post-update-hook when calling `lake update -R` (in the game's folder), but if this fails, you can always build it manually by calling `lake build gameserver`.
(both commands are to be executed in the game's directory!)

## Modifying the server

### Starting the server

When using the [manual installation](running_locally.md#manual-installation) you can run the server
using

```
npm start
```

This way any changes to files in `client/` or `relay/` will cause the server to restart automatically.

Alternative, you can run `npm run build` followed by the commands

```
npm run start_client
npm run production
```

(in two separate terminals) to test the production mode of the server. This way it will only
change once you build and restart the server.

### Modifying the lean server

To test a modified lean server (i.e. content of `server/`), you can use the local dev setup and call
`lake update -R -Klean4game.local` in your game followed by `lake build`.
This will cause lake to look for the
local lean server as a dependency instead of the version it downloaded from git.

You can play a local game at https://localhost:3000/#/g/local/{FolderName} where you replace `{FolderName}` with the game folder name.

After modifications in `server/`, you will need to call `lake build gameserver` (called in `server/` or in your game's folder) to rebuild
the gameserver executable and
`lake build` (called in the game's folder) to rebuild the game.
