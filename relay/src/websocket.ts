import anonymize from 'ip-anonymize';
import os from 'os';
import * as rpc from 'vscode-ws-jsonrpc';
import * as jsonrpcserver from 'vscode-ws-jsonrpc/server';
import { WebSocket } from 'ws';
import { ChildProcess } from 'child_process';
import { GameManager } from './serverProcess.js'
import { IncomingMessage } from 'http';

export class SocketListener {
  gameManager: GameManager
  socketCounter: number

  constructor(gameManager: GameManager) {
    this.gameManager = gameManager
    this.socketCounter = 0;
  };

  startObservedProcess(ws: WebSocket, req: IncomingMessage) {
    const ip = anonymize(req.headers['x-forwarded-for'] as string || req.socket.remoteAddress);
    let ps: ChildProcess = this.gameManager.startLeanServerProcessByRequest(req, ip)

    this.socketCounter++

    // This section is needed for games to start
    const socket: rpc.IWebSocket = {
      onMessage: (cb) => { ws.on("message", cb); },
      onError: (cb) => { ws.on("error", cb); },
      onClose: (cb) => { ws.on("close", cb); },
      send: (data) => { ws.send(data); },
      dispose: () => { }
    };
    const reader = new rpc.WebSocketMessageReader(socket);
    const writer = new rpc.WebSocketMessageWriter(socket);
    const socketConnection = jsonrpcserver.createConnection(reader, writer, () => ws.close());
    const serverConnection = jsonrpcserver.createProcessStreamConnection(ps);

    this.gameManager.devConnectionLog(socketConnection, serverConnection)
    socketConnection.onClose(() => serverConnection.dispose())
    serverConnection.onClose(() => socketConnection.dispose())


    console.log(`[${new Date()}] Number of open sockets - ${this.socketCounter}`);
    console.log(`[${new Date()}] Free RAM - ${Math.round(os.freemem() / 1024 / 1024)} / ${Math.round(os.totalmem() / 1024 / 1024)} MB`);

    ws.on('close', () => {
      console.log(`[${new Date()}] Socket closed - ${ip}`)
      this.socketCounter--
    });
  }
}
