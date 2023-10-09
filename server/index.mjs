import { WebSocketServer } from 'ws';
import express from 'express'
import path from 'path'
import * as cp from 'child_process';
import * as url from 'url';
import * as rpc from 'vscode-ws-jsonrpc';
import * as jsonrpcserver from 'vscode-ws-jsonrpc/server';
import os from 'os';
import anonymize from 'ip-anonymize';
// import { importTrigger, importStatus } from './import.mjs'

/** Preloaded games. The keys refer to the docker tags of the virtual machines.
 * The number `queueLength` determines how many instances of the docker container
 * get started before any user shows up to have them up and running immediately.
 * The values `name`, `module`, and `dir` are just used for development where we
 * use a project directory instead of a docker container.
*/
const games = {
    "g/hhu-adam/robo": {
        // module: "Game",  // The lean module's name. Defaults to "Game"
        // name: "Adam",    // For the `Game "Adam"` tag in the games. Defaults to "MyGame"
        dir: "Robo",
        queueLength: 5
    },
    "g/hhu-adam/nng4": {
        // module: "Game",
        // name: "NNG",
        dir: "NNG4",
        queueLength: 5
    },
    "g/hhu-adam/nng4-old": {
        dir: "NNG4-OLD",
        queueLength: 0
    },
    "g/local/game": {
        dir: "game",
        queueLength: 0
    }
}
// bd91db15ea40af33155abb7be486fed1b8110c58
const __filename = url.fileURLToPath(import.meta.url);
const __dirname = url.fileURLToPath(new URL('.', import.meta.url));

const app = express()

const PORT = process.env.PORT || 8080;

var router = express.Router();

// router.get('/import/status/:owner/:repo', importStatus)
// router.get('/import/trigger/:owner/:repo', importTrigger)

const server = app
  .use(express.static(path.join(__dirname, '../client/dist/')))
  .use('/', router)
  .listen(PORT, () => console.log(`Listening on ${PORT}`));

const wss = new WebSocketServer({ server })

var socketCounter = 0

const environment = process.env.NODE_ENV
const isDevelopment = environment === 'development'

/** We keep queues of started Lean Server processes to be ready when a user arrives */
const queue = {}

function startServerProcess(tag) {
    if (! games[tag]?.dir) {
        console.error(`Unknown game: ${tag}`)
        return
    }

    let serverProcess
    if (isDevelopment) {
        let args = ["--server", path.join("../../../../", games[tag].dir)]
        if (games[tag].module) {
            args.push(games[tag].module)
            if (games[tag].name) { args.push(games[tag].name) }
        }
        serverProcess = cp.spawn("./gameserver", args,
            { cwd: path.join(__dirname, "./build/bin/") })
    } else {
        serverProcess =  cp.spawn("./bubblewrap.sh",
            [games[tag].dir],
            { cwd: __dirname })
    }
    serverProcess.on('error', error =>
        console.error(`Launching Lean Server failed: ${error}`)
    );
    if (serverProcess.stderr !== null) {
        serverProcess.stderr.on('data', data =>
            console.error(`Lean Server: ${data}`)
        );
    }
    return serverProcess
}

/** start Lean Server processes to refill the queue */
function fillQueue(tag) {
    while (queue[tag].length < games[tag].queueLength) {
        const serverProcess = startServerProcess(tag)
        queue[tag].push(serverProcess)
    }
}

if (!isDevelopment) { // Don't use queue in development
    for (let tag in games) {
        queue[tag] = []
        fillQueue(tag)
    }
}

const urlRegEx = /^\/websocket\/g\/([\w.-]+)\/([\w.-]+)$/

wss.addListener("connection", function(ws, req) {
    const reRes = urlRegEx.exec(req.url)
    if (!reRes) { console.error(`Connection refused because of invalid URL: ${req.url}`); return; }
    const owner = reRes[1]
    const repo = reRes[2]
    const tag = `g/${owner.toLowerCase()}/${repo.toLowerCase()}`

    if (isDevelopment && process.env.DEV_CONTAINER) {
        tag = `g/local/game`
    }

    let ps;
    if (!queue[tag] || queue[tag].length == 0) {
        ps = startServerProcess(tag)
    } else {
        ps = queue[tag].shift() // Pick the first Lean process; it's likely to be ready immediately
        fillQueue(tag)
    }

    socketCounter += 1;
    const ip = anonymize(req.headers['x-forwarded-for'] || req.socket.remoteAddress)
    console.log(`[${new Date()}] Socket opened - ${ip}`)

    const socket = {
        onMessage: (cb) => { ws.on("message", cb) },
        onError: (cb) => { ws.on("error", cb) },
        onClose: (cb) => { ws.on("close", cb) },
        send: (data, cb) => { ws.send(data,cb) }
    }
    const reader = new rpc.WebSocketMessageReader(socket);
    const writer = new rpc.WebSocketMessageWriter(socket);
    const socketConnection = jsonrpcserver.createConnection(reader, writer, () => ws.close())
    const serverConnection = jsonrpcserver.createProcessStreamConnection(ps);
    socketConnection.forward(serverConnection, message => {
        if (isDevelopment) {console.log(`CLIENT: ${JSON.stringify(message)}`)}
        return message;
    });
    serverConnection.forward(socketConnection, message => {
      if (isDevelopment) {console.log(`SERVER: ${JSON.stringify(message)}`)}
        return message;
    });

    console.log(`[${new Date()}] Number of open sockets - ${socketCounter}`)
    console.log(`[${new Date()}] Free RAM - ${Math.round(os.freemem() / 1024 / 1024)} / ${Math.round(os.totalmem() / 1024 / 1024)} MB`)

    ws.on('close', () => {
      console.log(`[${new Date()}] Socket closed - ${ip}`)
      socketCounter -= 1;
    })

    socketConnection.onClose(() => serverConnection.dispose());
    serverConnection.onClose(() => socketConnection.dispose());
})
