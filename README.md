# Lean 4 Game

This is a prototype for a Lean 4 game platform. The project is based on ideas from the [Lean Game Maker](https://github.com/mpedramfar/Lean-game-maker) and the [Natural Number Game
(NNG)](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/)
of Kevin Buzzard and Mohammad Pedramfar.
The project is based on Patrick Massot's prototype: [NNG4](https://github.com/PatrickMassot/NNG4).

Building this requires a [npm](https://www.npmjs.com/) toolchain. After cloning the repository you should run
`npm install` to pull in all dependencies. For development and experimentation, you can run `npm start` that will perform a non-optimized build and then run a local webserver on port 3000.

### Progress & Contributing
Currently the interface is still undergoing bigger changes, contributions are of course welcome, but it might be better to wait with them for a bit until proper support for external games is implemented andthe existing games are separated from this repository. (ca. Sept. 2023)


### Documentation

For game developers, there is a work-in-progress Documentation: [Create a Game](DOCUMENTATION.md).
Best to talk with us directly.

For the game engine itself, the documentations is missing currently.

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

Developed using `node v19.3.0 (npm v9.2.0)`.

Install `nvm`
```
curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.2/install.sh | bash
```
then reopen bash and test with `command -v nvm` if it is available (Should print "nvm").

Now install node:
```
nvm install node
```
