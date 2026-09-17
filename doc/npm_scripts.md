## NPM Scripts

* `npm start`: Start the project in development mode. The browser will automatically reload when client files get changed. The Lean server will get recompiled and restarted when lean files get changed. The Lean server will be started without a container. The client and server can be started separately using the scripts `npm run start:client` and `npm run start:server`. The project can be accessed via `http://localhost:3000`.
Internally, websocket requests to `ws://localhost:3000/websockets` will be forwarded to a Lean server running on port `8080`.

* `npm run build`: Build the project in production mode. All assets of the client will be compiled into `client/dist`.
On the server side, the command will set up a docker image containing the Lean server. The two parts can be built separately using `npm run build:client` and `npm run build:server`.

* `npm run production`: Start the project in production mode. This requires that the build script has been run. It will start a server on the port specified in the `PORT` environment variable or by default on `8080`. You can run on a specific port by running `PORT=80 npm run production`. The server will serve the files in `client/dist` via http and give access to the bubblewrapped Lean server via the web socket protocol.

### Environment Variables

Some parts of the project can be configured using environment variables.

### Client

For example for `npm start`, `npm start:client`.

| name | values | default | description |
| ---- | ------ | ------- | ----------- |
| `CLIENT_PORT` | a number | `3000`  | sets the port for the client server |
| `VITE_CLIENT_DEFAULT_LANGUAGE` | ISO language key | `en` | sets the default language for the application |
| ... |  |  | TODO |

### Server

For example for `npm start`, `npm run production`, `npm run start:relay`.

| name | values | default | description |
| ---- | ------ | ------- | ----------- |
| `PORT` | Port number | `8080` | sets the port for the backend server |
| `API_PORT` | Port number | `undefined` | sets the port for the separate API server |
| `NODE_ENV` | `development`, `production` | set by npm scripts | Selects development or production behavior. |
| `GAME_ACTIVITY_FILE` | file path | `games/.lean4game/activity.json` | Optional path for the game activity metadata file. |
| `LEAN4GAME_GITHUB_USER` | GitHub username | not set | GitHub username sent with GitHub artifact download requests. |
| `LEAN4GAME_GITHUB_TOKEN` | GitHub access token | not set | Token used to request and download game artifacts from GitHub. For public games, a read-only token is enough. |
| `ISSUE_CONTACT` | URL | not set | Link shown when an import cannot start because of the disk-space check. |
| `RESERVED_DISC_SPACE_MB` | number of megabytes | not set | Value used by the disk-space check before importing a game artifact. |
| `NO_BWRAP` | `true`, `false` | `false` | to disable to use of `bubblewrap` in production mode. This means `Lean` runs without any container on your system, which imposes a security risk! |

#### API

In production, `/api/game-activity` is not exposed on the public server. It is available on the separate API server configured with `API_PORT`, together with `/api/game-sessions`.

The `/api/game-activity` endpoint lists all games known to the activity registry, including games that are not shown on the landing page.
