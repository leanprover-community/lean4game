import { WebSocketServer } from 'ws';
import express from 'express'
import path from 'path'
import * as cp from 'child_process';
import * as url from 'url';
import * as rpc from 'vscode-ws-jsonrpc';
import * as jsonrpcserver from 'vscode-ws-jsonrpc/server';


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

let cmd, cmdArgs, cwd;
if (isDevelopment) {
    cmd = "./gameserver";
    cmdArgs = ["--server"];
    cwd = "./leanserver/build/bin/"
} else{
    cmd = "docker";
    cmdArgs = ["run", "--runtime=runsc", "--network=none", "--rm", "-i", "testgame:latest"];
    cwd = "."
}

/** We keep a queue of started Lean Server processes to be ready when a user arrives */
const queue = []
const queueLength = 5

function startServerProcess() {
    const serverProcess = cp.spawn(cmd, cmdArgs, { cwd })
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
function fillQueue() {
    while (queue.length < queueLength) {
        const serverProcess = startServerProcess()
        queue.push(serverProcess)
    }
}

fillQueue()

wss.addListener("connection", function(ws) {
    let ps;
    if (isDevelopment) { // Don't use queue in development
        ps = startServerProcess()
    } else {
        ps = queue.shift() // Pick the first Lean process; it's likely to be ready immediately
        fillQueue()
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
