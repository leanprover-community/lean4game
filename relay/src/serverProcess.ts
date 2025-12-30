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
      console.error(`[${new Date()}]server process is undefined/null`);
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
          "./" + path.basename(customLeanServer),
          ["--server", game_dir],
          { cwd: path.dirname(customLeanServer) }
        );
      } else {
        serverProcess = cp.spawn("lake", ["serve", "--"], { cwd: game_dir });
      }
    } else {
      let cmd = "../../scripts/bubblewrap.sh"
      let options = [game_dir, customLeanServer ? "true" : "false"]
      if (owner == "test") {
        // TestGame doesn't have its own copy of the server and needs lean4game as a local dependency
        const lean4GameFolder = path.join(this.dir, '..', '..', '..', 'server')
        options.push(`--bind ${lean4GameFolder} /server`)
      }

      serverProcess = cp.spawn(cmd, options,
        { cwd: this.dir });
    }

    serverProcess.on('error', error => console.error(`[${new Date()}] Launching Lean Server failed: ${error}`));
    if (serverProcess.stderr !== null) {
      serverProcess.stderr.on('data', data => console.error(`[${new Date()}] Lean Server: ${data}`)
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
        console.error(`[${new Date()}] serverProcess was undefined/null`);
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

    let shift = (line: number, offset: number) => Math.max(0, line + offset)

    let shiftLines = (p : any, offset : number) => {
      if (p.hasOwnProperty("line")) {
        p.line = shift(p.line, offset)
      }
      if (p.hasOwnProperty("lineRange")) {
        p.lineRange.start = shift(p.lineRange.start, offset)
        p.lineRange.end = shift(p.lineRange.end, offset)
      }
      for (let key in p) {
        if (typeof p[key] === 'object' && p[key] !== null) {
          p[key] = shiftLines(p[key], offset);
        }
      }
      return p;
    }

    function replaceUri(obj: object, val: string) {
      for (const key in obj) {
        if (key === 'uri') {
          obj[key] = val;
        } else if (typeof obj[key] === 'object' && obj[key] !== null) {
          replaceUri(obj[key], val);
        }
      }
      return obj
    }


    // These values will be set by the initialize message
    let difficulty: number
    let inventory: string[]
    let worldId: string
    let levelId: string

    let semanticTokenRequestIds = new Set<number>()

    const PROOF_START_LINE = 2

    const gameDataPath = path.join(gameDir, '.lake', 'gamedata', `game.json`)
    const gameData = JSON.parse(fs.readFileSync(gameDataPath, 'utf8'))

    /** Sending messages from the client to the server */
    socketConnection.forward(serverConnection, (message: any) => {

      // backwards compatibility for versions ≤ v4.7.0
      if (usesCustomLeanServer) {
        if (isDevelopment) { console.log(`CLIENT: ${JSON.stringify(message)}`); }
        return message
      }

      if (message.method === "initialize") {
        difficulty = message.params.initializationOptions.difficulty
        inventory = message.params.initializationOptions.inventory
        // We abuse the rootUri field to pass the game name to the server
        message.params.rootUri = gameData.name
      }

      if (message.method === "textDocument/semanticTokens/full") {
        semanticTokenRequestIds.add(message.id)
      }

      if (message.method === "textDocument/didOpen") {
        // Parse the URI to get world and level
        const uri = new URL(message.params.textDocument.uri)
        const pathParts = path.parse(uri.pathname)
        worldId = path.basename(pathParts.dir)
        levelId = pathParts.name

        replaceUri(message, `file://${gameDir}/Game/Metadata.lean`)

        // Read level data from JSON file
        const levelDataPath = path.join(gameDir, '.lake', 'gamedata', `level__${worldId}__${levelId}.json`)
        const levelData = JSON.parse(fs.readFileSync(levelDataPath, 'utf8'))

        if (difficulty === undefined || inventory === undefined) {
          console.error("Did not receive difficulty/inventory from client!")
          difficulty = 1
          inventory = []
        }

        let content = message.params.textDocument.text;
        message.params.textDocument.text =
          `import ${levelData.module} import GameServer.Runner \nRunner ` +
          `${JSON.stringify(gameData.name)} ${JSON.stringify(worldId)} ${levelId} ` +
          `(difficulty := ${difficulty}) ` +
          `(inventory := [${inventory.map(s => JSON.stringify(s)).join(',')}]) ` +
          `:= by\n${content}\n`
      } else {
        replaceUri(message, `file://${gameDir}/Game/Metadata.lean`)
      }

      shiftLines(message, +PROOF_START_LINE)

      // Print the message as the server will receive it
      if (isDevelopment) { console.log(`CLIENT: ${JSON.stringify(message)}`); }

      return message
    });


    /** Sending messages from the server to the client */
    serverConnection.forward(socketConnection, message => {

      // Print the message as the server sends it
      if (isDevelopment) { console.log(`SERVER: ${JSON.stringify(message)}`); }

      // backwards compatibility for versions ≤ v4.7.0
      if (usesCustomLeanServer) return message

      shiftLines(message, -PROOF_START_LINE);
      replaceUri(message, `file:///${worldId}/${levelId}.lean`) // as defined in `level.tsx`

      // Disable range semantic tokens because they are difficult to shift
      if ((message as any)?.result?.capabilities?.semanticTokensProvider?.range) {
        (message as any).result.capabilities.semanticTokensProvider.range = false
      }

      // Shift semantic tokens (https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_semanticTokens)
      if (semanticTokenRequestIds.delete((message as any)?.id)) {
        const data : number[] = (message as any).result.data
        let i = 0
        let newData = []
        let line = 0
        // Search for semantic tokens at or after PROOF_START_LINE
        while (i < data.length) {
          line += data[i] // line info is a delta
          if (line >= PROOF_START_LINE) {
            // Relevant tokens start here. Copy them.
            newData = data.slice(i);
            // Adjust the first line number to be relative to the proof
            newData[0] = line - PROOF_START_LINE;
            break;
          }
          i += 5 // Line info is on every fifth entry
        }
        (message as any).result.data = newData
      }

      return message
    });
  }

  getGameDir(owner: string, repo: string) {
    owner = owner.toLowerCase();
    if (owner == 'local' && !isDevelopment) {
      console.error(`[${new Date()}] No local games in production mode.`);
      return "";
    }

    let game_dir: string
    if(owner == 'local') {
      game_dir = path.join(this.dir, '..', '..', '..', '..', repo)
    } else if (owner == 'test') {
      game_dir = path.join(this.dir, '..', '..', '..', 'cypress', repo)
      console.debug(game_dir)
    } else {
      const gamesPath = path.join(this.dir, '..', '..', '..', 'games');
      if (!fs.existsSync(gamesPath)) {
        console.error(`[${new Date()}] Did not find the following folder: ${gamesPath}`);
        console.error(`[${new Date()}] Did you already import any games?`);
        return "";
      }
      game_dir = path.join(gamesPath, `${owner}`, `${repo.toLowerCase()}`);
    }

    if (!fs.existsSync(game_dir)) {
      console.error(`[${new Date()}] Game '${game_dir}' does not exist!`);
      return "";
    }

    let game_json: string = path.join(game_dir, ".lake", "gamedata", "game.json")

    if (!fs.existsSync(game_json)) {
      console.error(`[${new Date()}] game.json file does not exist for ${owner}/${repo}!`);
      return "";
    }

    return game_dir;
  }

  getTagString(tag: Tag) {
    return `g/${tag.owner.toLowerCase()}/${tag.repo.toLowerCase()}`;
  }
}
