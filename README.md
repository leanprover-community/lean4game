# Lean 4 Game

This is a prototype for a Lean 4 game platform. It is based on ideas from the [Lean Game Maker](https://github.com/mpedramfar/Lean-game-maker) and the [Natural Number Game
(NNG)](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/)
of Kevin Buzzard and Mohammad Pedramfar.
The project is currently mostly copied from Patrick Massot's [NNG4](https://github.com/PatrickMassot/NNG4), but we plan to extend it significantly.

Building this requires a [npm](https://www.npmjs.com/) toolchain. After cloning the repository you should run
`npm install` to pull in all dependencies. For development and experimentation, you can run `npm start` that will perform a non-optimized build and then run a local webserver on port 3000.

### Progress
This is a work in progress. In the future there are plans to host a server managing different public learning games for Lean4, but for now the target is to provide the first games (in German and eventually English) by April 2023.

## NPM Scripts

* `npm start`: Start the project in development mode. The browser will automatically reload when client files get changed. The Lean server will get recompiled and restarted when lean files get changed. The Lean server will be started without a container. The client and server can be started separately using the scripts `npm run start_client` and `npm run start_server`. The project can be accessed via `http://localhost:3000`.
Internally, websocket requests to `ws://localhost:3000/websockets` will be forwarded to a Lean server running on port `8080`.

* `npm run build`: Build the project in production mode. All assets of the client will be compiled into `client/dist`.
On the server side, the command will set up a docker image containing the Lean server. The two parts can be built separately using `npm run build_client` and `npm run build_server`.

* `npm run production`: Start the project in production mode. This requires that the build script has been run. It will start a server on the port specified in the `PORT` environment variable or by default on `8080`. You can run on a specifiv port by running `PORT=80 npm run production`. The server will serve the files in `client/dist` via http and give access to the docker-contained Lean server via the web socket protocol.


## Security

Providing the use access to a Lean instance running on the server is a severe security risk. That is why we start the Lean server in a Docker container
secured by [gVisor](https://gvisor.dev/).


## Detailed installation notes

### Node.js

Developed using `node v18.12.1 (npm v8.19.2)`.

Install `nvm`
```
curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.2/install.sh | bash
```
then reopen bash and test with `command -v nvm` if it is available (Should print "nvm").

Now install node:
```
nvm install node --lts
```
