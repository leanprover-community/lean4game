import * as cp from 'child_process';
import { ChildProcess } from 'child_process';
import { IncomingMessage } from 'http';
import * as jsonrpcserver from 'vscode-ws-jsonrpc/server';
import fs from 'fs';
import path from 'path';

type Tag = { owner: string; repo: string; };
export type GameSession = { process: ChildProcess, game: string}
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

    if (!this.queue[tag] || this.queue[tag].length == 0) {
      ps = this.createGameProcess(reResTag.owner, reResTag.repo);
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

    return {process: ps, game: game}
  }

  createGameProcess(owner, repo) {
    let game_dir = this.getGameDir(owner, repo);
    if (!game_dir) return;

    let serverProcess: cp.ChildProcessWithoutNullStreams;
    if (isDevelopment) {
      let args = ["--server", game_dir];
      let binDir = path.join(game_dir, ".lake", "packages", "GameServer", "server", ".lake", "build", "bin");
      // Note: `cwd` is important to be the `bin` directory as `Watchdog` calls `./gameserver` again
      if (fs.existsSync(binDir)) {
        // Try to use the game's own copy of `gameserver`.
        serverProcess = cp.spawn("./gameserver", args, { cwd: binDir });
      } else {
        // If the game is built with `-Klean4game.local` there is no copy in the lake packages.
        serverProcess = cp.spawn("./gameserver", args,
          { cwd: path.join(this.dir, "..", "..", "..", "server", ".lake", "build", "bin") });
      }
    } else {
      serverProcess = cp.spawn("../../scripts/bubblewrap.sh",
        [game_dir, path.join(this.dir, '..')],
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
      serverProcess = this.createGameProcess(tag.owner, tag.repo);
      if (serverProcess == null) {
        console.error('serverProcess was undefined/null');
        return;
      }
      this.queue[tagString].push(serverProcess);
    }
  }

  devConnectionLog(socketConnection: jsonrpcserver.IConnection, serverConnection: jsonrpcserver.IConnection) {
    socketConnection.forward(serverConnection, message => {
      if (isDevelopment) { console.log(`CLIENT: ${JSON.stringify(message)}`); }
      return message;
    });
    serverConnection.forward(socketConnection, message => {
      if (isDevelopment) { console.log(`SERVER: ${JSON.stringify(message)}`); }
      return message;
    });
  }

  getGameDir(owner: string, repo: string) {
    owner = owner.toLowerCase();
    if (owner == 'local') {
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
