import { WebSocketServer } from 'ws';
import express from 'express'
import path from 'path'
import * as cp from 'child_process';
import * as url from 'url';
import * as rpc from 'vscode-ws-jsonrpc';
import * as jsonrpcserver from 'vscode-ws-jsonrpc/server';

const games = {
    testgame: {
        name: "TestGame",
        module: "TestGame",
        queueLength: 5
    },
    nng: {
        name: "NNG",
        module: "NNG",
        queueLength: 5
    }
}

const __filename = url.fileURLToPath(import.meta.url);
const __dirname = url.fileURLToPath(new URL('.', import.meta.url));

const app = express()

const PORT = process.env.PORT || 8080;

const server = app
  .use(express.static(path.join(__dirname, '../client/dist/')))
  .listen(PORT, () => console.log(`Listening on ${PORT}`));

const wss = new WebSocketServer({ server })

const environment = process.env.NODE_ENV
const isDevelopment = environment === 'development'

/** We keep queues of started Lean Server processes to be ready when a user arrives */
const queue = {}
const queueLength = 5

function startServerProcess(gameId) {
    const serverProcess = isDevelopment
        ? cp.spawn("./gameserver",
            ["--server", gameId, games[gameId].module, games[gameId].name],
            { cwd: "./leanserver/build/bin/" })
        : cp.spawn("docker",
            ["run", "--runtime=runsc", "--network=none", "--rm", "-i", `${gameId}:latest`],
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
        console.log(`CLIENT: ${JSON.stringify(message)}`)
        return message;
    });
    serverConnection.forward(socketConnection, message => {
        console.log(`SERVER: ${JSON.stringify(message)}`)
        return message;
    });
    socketConnection.onClose(() => serverConnection.dispose());
    serverConnection.onClose(() => socketConnection.dispose());
})
