import anonymize from 'ip-anonymize';
import * as jsonrpcserver from 'vscode-ws-jsonrpc/server';
import { IWebSocket, WebSocketMessageReader, WebSocketMessageWriter } from 'vscode-ws-jsonrpc';
import { WebSocket, WebSocketServer } from 'ws';
import { ChildProcess } from 'child_process';
import { GameManager, GameSession } from './serverProcess.js'
import { IncomingMessage } from 'http';
import { randomUUID, UUID } from 'crypto';

interface Player {
  id: UUID,
  currentGame: string
  anonIP: string
  lang: string
  process: ChildProcess
}

interface PlayerMeasurement {
  date: Array<Date>
  anon_Ip: Array<string>
  game: Array<string>
  lang: Array<string>
}

export class GameSessionsObserver {
  gameManager: GameManager
  wss: WebSocketServer
  players: Map<WebSocket, Player>
  socketCounter: number

  constructor(gameManager: GameManager, wss: WebSocketServer) {
    this.gameManager = gameManager
    this.wss = wss
    this.players = new Map<WebSocket, Player>()
    this.socketCounter = 0
  }

  /**
   * Return information about all current open game sessions on the server.
   * @returns A PlayerMeasurement object containing all current open game sessions
   */
  getAllConnectedPlayers(): PlayerMeasurement {
    const webSockets: Array<WebSocket> = this.getAllOpenWebSockets()
    const timestamp = new Date()

    let measurement: PlayerMeasurement = {
      date: new Array<Date>(),
      anon_Ip: new Array<string>(),
      game: new Array<string>(),
      lang: new Array<string>()
    }

    /**
     * Iterate over every open websocket of the server
     * while checking if the socket corresponds to player.
     * If the socket is corresponding to a player add the
     * player's information to the PlayerMeasuremnt intance.
     */
    webSockets.forEach( (ws) => {
      const player = this.players.get(ws)
      if (player != undefined) {
        measurement.date.push(timestamp)
        measurement.anon_Ip.push(player.anonIP)
        measurement.game.push(player.currentGame)
        measurement.lang.push(player.lang)
      }
    })

    return measurement
  }

  /**
   * Start a game process on the server and add the player to the list
   * of currently active players until the player leaves the game.
   * @param ws
   * @param req
   * @param wss
   */
  startObservedGame(ws: WebSocket, req: IncomingMessage) {
    const headers = req.headers['x-forwarded-for']
    const ip = anonymize(((Array.isArray(headers) ? headers[0] : headers) ?? req.socket.remoteAddress) ?? "") ?? ""
    let gameSession: GameSession | undefined = this.gameManager.startGame(req, ip)

    if (!gameSession) return // TODO: can this happen? do we need to do anytthing here?

    let ps = gameSession.process
    let game = gameSession.game
    let gameDir = gameSession.gameDir

    const langRegex: RegExp = /^[a-zA-Z-]+(?=,)/
    let lang = "en-US"

    const accept_lang = req.headers['accept-language']
    if(accept_lang && langRegex.exec(accept_lang) !== null) {
      const newLang = langRegex.exec(accept_lang)
      if (newLang) {
        lang = newLang[0]
      }
    }

    this.addPlayerConnection(ws, game, ip, ps, lang);

    //this.socketCounter++

    const socket: IWebSocket = {
      onMessage: (cb) => { ws.on("message", cb); },
      onError: (cb) => { ws.on("error", cb); },
      onClose: (cb) => { ws.on("close", cb); },
      send: (data) => { ws.send(data); },
      dispose: () => { }
    }

    const reader = new WebSocketMessageReader(socket);
    const writer = new WebSocketMessageWriter(socket);
    const socketConnection = jsonrpcserver.createConnection(reader, writer, () => {
      ws.close()
    });
    const player = this.players.get(ws)
    if (!player) return
    const serverConnection = jsonrpcserver.createProcessStreamConnection(player.process);
    if (!serverConnection) return
    this.gameManager.messageTranslation(
      socketConnection, serverConnection, gameDir, gameSession.usesCustomLeanServer
    )

    socketConnection.onClose(() => {
      serverConnection.dispose()
    })
    serverConnection.onClose(() => {
      socketConnection.dispose()
    })

    //console.log(`[${new Date()}] Number of open sockets - ${this.socketCounter}`);
    //console.log(`[${new Date()}] Free RAM - ${Math.round(os.freemem() / 1024 / 1024)} / ${Math.round(os.totalmem() / 1024 / 1024)} MB`);

    ws.on('close', () => {
      const player = this.players.get(ws)
      this.players.delete(ws)
      //this.socketCounter-- // TODO?: why is this commented out?
      if (player) {
        console.log(`[${new Date()}] Socket closed by ${ip} on ${player.currentGame}`)
      } else {
        console.log(`[${new Date()}] Tried to close non-existing socket by ${ip}`)
      }
    })
  }

  /**
   * Return all open WebSocket connections to the server
   * @returns Array of WebSocket objects
   */
  private getAllOpenWebSockets() {
    return Array.from(this.wss.clients);
  }

  private addPlayerConnection(ws: WebSocket, game: string, ip: string, ps: ChildProcess, lang: string) {
    let playerId: UUID = randomUUID();
    this.players.set(ws, {
      id: playerId,
      currentGame: game,
      anonIP: ip,
      lang: lang,
      process: ps
    }
    );
  }
}
