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
| `PORT` | a number | `8080` | sets the port for the backend server |
| `API_PORT` | a number | `undefined` | TODO: describe |
| `NO_BWRAP` | `true`, `false` | `false` | to disable to use of `bubblewrap` in production mode. This means `Lean` runs without any container on your system, which imposes a security risk! |
| ... |  |  | TODO |
