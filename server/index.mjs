import { WebSocketServer } from 'ws';
import express from 'express'
import path from 'path'
import { spawn } from 'child_process';
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

let cmd, cmdArgs;
if (isDevelopment) {
    cmd = "./leanserver/build/bin/gameserver";
    cmdArgs = ["--server"];
} else{
    cmd = "docker";
    cmdArgs = ["run", "--runtime=runsc", "--network=none", "--rm", "-i", "testgame:latest"];
}

wss.addListener("connection", function(ws) {
    const socket = {
        onMessage: (cb) => {ws.on("message", cb)},
        onError: (cb) => {ws.on("error", cb)},
        onClose: (cb) => {ws.on("onclose", cb)},
        send: ws.send
    }
    const reader = new rpc.WebSocketMessageReader(socket);
    const writer = new rpc.WebSocketMessageWriter(socket);
    const socketConnection = jsonrpcserver.createConnection(reader, writer, () => ws.close())
    const serverConnection = jsonrpcserver.createServerProcess('Lean Server', cmd, cmdArgs);
    jsonrpcserver.forward(socketConnection, serverConnection, message => {
        return message;
    });
})
