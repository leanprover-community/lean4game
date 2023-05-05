import { WebSocketServer } from 'ws';
import express from 'express'
import path from 'path'
import * as cp from 'child_process';
import * as url from 'url';
import * as rpc from 'vscode-ws-jsonrpc';
import * as jsonrpcserver from 'vscode-ws-jsonrpc/server';
import os from 'os';
import anonymize from 'ip-anonymize';
import { importTrigger, importStatus } from './import.mjs'

const games = {
    adam: {
        name: "Adam",
        module: "Adam",
        dir: "../../../../Robo",
        queueLength: 5
    },
    nng: {
        name: "NNG",
        module: "NNG",
        dir: "../../../../NNG4",
        queueLength: 5
    }
}

const __filename = url.fileURLToPath(import.meta.url);
const __dirname = url.fileURLToPath(new URL('.', import.meta.url));

const app = express()

const PORT = process.env.PORT || 8080;

var router = express.Router();

router.get('/import/status/:owner/:repo', importStatus)
router.get('/import/trigger/:owner/:repo', importTrigger)

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
const queueLength = 5

function startServerProcess(gameId) {
    const serverProcess = isDevelopment
        ? cp.spawn("./gameserver",
            ["--server", games[gameId].dir, games[gameId].module, games[gameId].name],
            { cwd: "./build/bin/" })
        : cp.spawn("docker",
            ["run", "--runtime=runsc", "--network=none", "--rm", "-i", `${gameId}:latest`,
              "./gameserver", "--server", "/game/", games[gameId].module, games[gameId].name],
            { cwd: "." })
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
function fillQueue(gameId) {
    while (queue[gameId].length < games[gameId].queueLength) {
        const serverProcess = startServerProcess(gameId)
        queue[gameId].push(serverProcess)
    }
}

for (let gameId in games) {
    queue[gameId] = []
    fillQueue(gameId)
}

const urlRegEx = new RegExp("^/websocket/(.*)$")

wss.addListener("connection", function(ws, req) {
    const reRes = urlRegEx.exec(req.url)
    if (!reRes) { console.error(`Connection refused because of invalid URL: ${req.url}`); return; }
    const gameId = reRes[1]
    if (!games[gameId]) { console.error(`Unknown game: ${gameId}`); return; }

    let ps;
    if (isDevelopment) { // Don't use queue in development
        ps = startServerProcess(gameId)
    } else {
        ps = queue[gameId].shift() // Pick the first Lean process; it's likely to be ready immediately
        fillQueue(gameId)
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
    console.log(`[${new Date()}] Free RAM - ${Math.round(os.freemem() / 1024 / 1024)} / ${Math.round(os.totalmem() / 1024 / 1024)} GB`)

    ws.on('close', () => {
      console.log(`[${new Date()}] Socket closed - ${ip}`)
      socketCounter -= 1;
    })

    socketConnection.onClose(() => serverConnection.dispose());
    serverConnection.onClose(() => socketConnection.dispose());
})
