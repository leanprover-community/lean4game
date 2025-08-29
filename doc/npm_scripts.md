## NPM Scripts

* `npm start`: Start the project in development mode. The browser will automatically reload when client files get changed. The Lean server will get recompiled and restarted when lean files get changed. The Lean server will be started without a container. The client and server can be started separately using the scripts `npm run start:client` and `npm run start:server`. The project can be accessed via `http://localhost:3000`.
Internally, websocket requests to `ws://localhost:3000/websockets` will be forwarded to a Lean server running on port `8080`.

* `npm run build`: Build the project in production mode. All assets of the client will be compiled into `client/dist`.
On the server side, the command will set up a docker image containing the Lean server. The two parts can be built separately using `npm run build:client` and `npm run build:server`.

* `npm run production`: Start the project in production mode. This requires that the build script has been run. It will start a server on the port specified in the `PORT` environment variable or by default on `8080`. You can run on a specific port by running `PORT=80 npm run production`. The server will serve the files in `client/dist` via http and give access to the bubblewrapped Lean server via the web socket protocol.

### Environment Variables

The client and server ports, as well as the default language, can be configured using environment variables:

* `PORT`: Sets the port for the backend server (default: `8080`).
* `CLIENT_PORT`: Sets the port for the client server (default: `3000`).
* `VITE_CLIENT_DEFAULT_LANGUAGE`: Sets the default language for the application (default: `en`).

Ensure these environment variables are set appropriately in your environment to configure the project as needed.
