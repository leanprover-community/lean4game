import * as cp from 'child_process';
import { ChildProcess } from 'child_process';
import { IncomingMessage } from 'http';
import * as jsonrpcserver from 'vscode-ws-jsonrpc/server';
import fs from 'fs';
import path from 'path';

type Tag = { owner: string; repo: string; };
export type GameSession = {
  process: ChildProcess,
  game: string,
  gameDir: string,
  usesCustomLeanServer: boolean
}
const environment = process.env.NODE_ENV;
const isDevelopment = environment === 'development';

export class GameManager {
  queueLength: {}
  queue: {}
  urlRegEx: RegExp
  dir: string

  constructor(directory: string) {
    /**
     * Add a game here if the server should keep a queue of pre-loaded games ready at all times.
     *
     * IMPORTANT! Tags here need to be lower case!
    */
    this.queueLength = {
      "g/hhu-adam/robo": 2,
      "g/leanprover-community/nng4": 5,
      "g/djvelleman/stg4": 2,
      "g/trequetrum/lean4game-logic": 2,
    };
    /** We keep queues of started Lean Server processes to be ready when a user arrives */
    this.queue = {};
    this.urlRegEx = /^\/websocket\/g\/([\w.-]+)\/([\w.-]+)$/;
    this.dir = directory
  }

  startGame(req: IncomingMessage, ip: string): GameSession{
    let ps: ChildProcess
    const reRes = this.urlRegEx.exec(req.url);

    if (!reRes) { console.error(`Connection refused because of invalid URL: ${req.url}`); return; }
    const reResTag: Tag = { owner: reRes[1], repo: reRes[2] };
    const tag = this.getTagString(reResTag);
    const game = `${reResTag.owner}/${reResTag.repo}`
    const customLeanServer = this.getCustomLeanServer(reResTag.owner, reResTag.repo)

    if (!this.queue[tag] || this.queue[tag].length == 0) {
      ps = this.createGameProcess(reResTag.owner, reResTag.repo, customLeanServer);
      // TODO (Matvey): extract further information from `req`, for example browser language.
      console.log(`[${new Date()}] Socket opened by ${ip} on ${game}`);
    } else {
      console.info('Got process from the queue');
      ps = this.queue[tag].shift(); // Pick the first Lean process; it's likely to be ready immediately
      this.fillQueue(reResTag);
    }

    if (ps == null) {
      console.error('server process is undefined/null');
      return;
    }

    const gameDir = this.getGameDir(reResTag.owner, reResTag.repo)

    return {process: ps, game: game, gameDir: gameDir, usesCustomLeanServer: customLeanServer !== null }
  }

  getCustomLeanServer(owner, repo) : string | null {
    let gameDir = this.getGameDir(owner, repo);
    let binary = path.join(gameDir, ".lake", "packages", "GameServer", "server", ".lake", "build", "bin", "gameserver");
    if (fs.existsSync(binary)) {
      return binary
    } else {
      return null
    }
  }

  createGameProcess(owner: string, repo: string, customLeanServer: string | null) {
    let game_dir = this.getGameDir(owner, repo);
    if (!game_dir) return;

    let serverProcess: cp.ChildProcessWithoutNullStreams;
    if (isDevelopment) {
      if (customLeanServer) {
        // If the game still uses a custom Lean server, use it.
        // Note: `cwd` is important to be the `bin` directory as `Watchdog` calls `./gameserver` again
        serverProcess = cp.spawn(
          path.join(".", path.basename(customLeanServer)),
          ["--server", game_dir],
          { cwd: path.dirname(customLeanServer) }
        );
      } else {
        serverProcess = cp.spawn("lake", ["serve", "--"], { cwd: game_dir });
      }
    } else {
      console.log(path.dirname(customLeanServer))
      serverProcess = cp.spawn("../../scripts/bubblewrap.sh",
        [game_dir, path.join(this.dir, '..', '..', '..'), customLeanServer ? "true" : "false"],
        { cwd: this.dir });
    }

    serverProcess.on('error', error => console.error(`Launching Lean Server failed: ${error}`)
    );
    if (serverProcess.stderr !== null) {
      serverProcess.stderr.on('data', data => console.error(`Lean Server: ${data}`)
      );
    }
    return serverProcess;
  }

  /**
   * start Lean Server processes to refill the queue
   */
  fillQueue(tag: { owner: string; repo: string; }) {
    const tagString = this.getTagString(tag);
    while (this.queue[tagString].length < this.queueLength[tagString]) {
      let serverProcess: cp.ChildProcessWithoutNullStreams;
      serverProcess = this.createGameProcess(
        tag.owner, tag.repo,
        this.getCustomLeanServer(tag.owner, tag.repo)
      );
      if (serverProcess == null) {
        console.error('serverProcess was undefined/null');
        return;
      }
      this.queue[tagString].push(serverProcess);
    }
  }

  messageTranslation(
    socketConnection: jsonrpcserver.IConnection,
    serverConnection: jsonrpcserver.IConnection,
    gameDir: string,
    usesCustomLeanServer: boolean
  ) {

    let shiftLines = (p : any, offset : number) => {
      if (p.hasOwnProperty("line")) {
        p.line = Math.max(0, p.line + offset)
      }
      if (p.hasOwnProperty("lineRange")) {
        p.lineRange.start = Math.max(0, p.lineRange.start + offset)
        p.lineRange.end = Math.max(0, p.lineRange.end + offset)
      }
      for (let key in p) {
        if (typeof p[key] === 'object' && p[key] !== null) {
          p[key] = shiftLines(p[key], offset);
        }
      }
      return p;
    }

    // These values will be set by the initialize message
    let difficulty: number
    let inventory: string[]

    const PROOF_START_LINE = 2

    const gameDataPath = path.join(gameDir, '.lake', 'gamedata', `game.json`)
    const gameData = JSON.parse(fs.readFileSync(gameDataPath, 'utf8'))

    socketConnection.forward(serverConnection, (message: any) => {

      if (isDevelopment) { console.log(`CLIENT: ${JSON.stringify(message)}`); }

      if (usesCustomLeanServer) return message

      if (message.method === "initialize") {
        difficulty = message.params.initializationOptions.difficulty
        inventory = message.params.initializationOptions.inventory
        // We abuse the rootUri field to pass the game name to the server
        message.params.rootUri = gameData.name
      }

      if (message.method === "textDocument/didOpen") {
        // Parse the URI to get world and level
        const uri = new URL(message.params.textDocument.uri)
        const pathParts = path.parse(uri.pathname)
        const worldId = path.basename(pathParts.dir)
        const levelId = pathParts.name

        // Read level data from JSON file
        const levelDataPath = path.join(gameDir, '.lake', 'gamedata', `level__${worldId}__${levelId}.json`)
        const levelData = JSON.parse(fs.readFileSync(levelDataPath, 'utf8'))

        let content = message.params.textDocument.text;
        message.params.textDocument.text =
          `import ${levelData.module} import GameServer.Runner Runner ` +
          `${JSON.stringify(gameData.name)} ${JSON.stringify(worldId)} ${levelId} ` +
          `(difficulty := ${difficulty}) ` +
          `(inventory := [${inventory.map(s => JSON.stringify(s)).join(',')}]) ` +
          `:= by\nskip\n${content}\n`
      }

      return shiftLines(message, +PROOF_START_LINE);
    });
    serverConnection.forward(socketConnection, message => {
      if (isDevelopment) { console.log(`SERVER: ${JSON.stringify(message)}`); }

      if (usesCustomLeanServer) return message

      return shiftLines(message, -PROOF_START_LINE);
    });
  }

  getGameDir(owner: string, repo: string) {
    owner = owner.toLowerCase();
    if (owner == 'local' || owner == 'test') {
      if (!isDevelopment) {
        console.error(`No local games in production mode.`);
        return "";
      }
    } else {
      const gamesPath = path.join(this.dir, '..', '..', '..', 'games');
      if (!fs.existsSync(gamesPath)) {
        console.error(`Did not find the following folder: ${gamesPath}`);
        console.error('Did you already import any games?');
        return "";
      }
    }

    let game_dir: string
    if(owner == 'local') {
      game_dir = path.join(this.dir, '..', '..', '..', '..', repo)
    } else if (owner == 'test') {
      game_dir = path.join(this.dir, '..', '..', '..', 'cypress', repo)
    } else {
      game_dir = path.join(this.dir, '..', '..', '..', 'games', `${owner}`, `${repo.toLowerCase()}`);
    }

    if (!fs.existsSync(game_dir)) {
      console.error(`Game '${game_dir}' does not exist!`);
      return "";
    }

    return game_dir;
  }

  getTagString(tag: Tag) {
    return `g/${tag.owner.toLowerCase()}/${tag.repo.toLowerCase()}`;
  }
}
