import express from 'express'
import path from 'path'
import * as url from 'url';
import fs from 'fs';
import anonymize from 'ip-anonymize';
import { importTrigger, importStatus } from './import.js'
import process from 'process';
import { spawn } from 'child_process'
import { GameManager } from './serverProcess.js';
import { GameSessionsObserver } from './websocket.js';
import { WebSocketServer } from 'ws';
// import fs from 'fs'
// const __filename = url.fileURLToPath(import.meta.url);

const __dirname: string = url.fileURLToPath(new URL('.', import.meta.url));
const clientDistPath: string = path.join(__dirname, '..', '..', '..', 'client', 'dist');
const app = express()
const gameManager = new GameManager(__dirname)
const PORT = process.env.PORT || 8080
const API = process.env.API_PORT

const environment = process.env.NODE_ENV;
const isDevelopment = environment === 'development';

let router = express.Router();
router.get('/import/status/:owner/:repo', importStatus)
router.get('/import/trigger/:owner/:repo', importTrigger)

const server = app
  .use(express.static(clientDistPath)) // TODO: add a dist folder from inside the game
  .use('/i18n/g/:owner/:repo/:lang', (req, res, next) => {
    const owner = req.params.owner;
    const repo = req.params.repo
    const lang = req.params.lang

    const anon_ip = anonymize(req.headers['x-forwarded-for'] as string || req.socket.remoteAddress)
    const log = path.join(process.cwd(), 'logs', 'game-access.log')
    const header = "date;anon-ip;game;lang\n"
    const data = `${new Date()};${anon_ip};${owner}/${repo};${lang}\n`

    fs.mkdir(path.join(process.cwd(), 'logs'), { recursive: true }, (err) => {
      if (err) console.log("Failed to create logs directory!")
      else {
        // 'ax' fails if the file already exists: https://nodejs.org/api/fs.html#file-system-flags
        fs.writeFile(log, header.concat(data), { flag: 'ax' }, (file_exists) => {
          if (file_exists) {
            fs.appendFile(log, data, (err) => {
              if (err) console.log(`Failed to append to log: ${err}`)
            });
          }
        });
      }
    });

    console.log(`[${new Date()}] ${anon_ip} requested translation for ${owner}/${repo} in ${lang}`)

    req.url = "Game.json";
    const staticHandler = express.static(
      path.join(gameManager.getGameDir(owner, repo), ".i18n", lang),
      { fallthrough: true }
    );
    staticHandler(req, res, (err) => {
      if (err) return next(err);
      // if missing, return empty json instead
      res.setHeader("Content-Type", "application/json");
      res.status(200).send("{}");
    });
  })
  .use('/data/g/:owner/:repo/*path', (req, res, next) => {
    const owner = req.params.owner;
    const repo = req.params.repo
    const filename = req.params.path.join('/');
    req.url = filename;
    console.debug(gameManager.getGameDir(owner,repo))
    const staticHandler = express.static(
      path.join(gameManager.getGameDir(owner,repo),".lake","gamedata"),
      { fallthrough: true }
    );
    staticHandler(req, res, (err) => {
      if (err) return next(err);
      // if missing, return empty json instead
      res.setHeader("Content-Type", "application/json");
      res.status(200).send("{}");
    });
  })
  .use('/data/stats', (req, res, next) => {
    // TODO: this throws on Windows
    const statsScriptPath = path.join(__dirname, "..", "..", "scripts", "stats.sh");
    const statsProcess = spawn('/bin/bash', [statsScriptPath, process.pid.toString()])
    let outputData = ''
    let errorData = ''
    statsProcess.stdout.on('data', (data) => {
      outputData += data.toString();
    })
    statsProcess.stderr.on('data', (data) => {
      errorData += data.toString();
    })
    statsProcess.on('close', (code) => {
      if (code === 0) {
        res.send(outputData);
      } else {
        res.status(500).send(`Error executing script: ${errorData}`)
        console.error(`[${new Date()}] stats.sh exited with code ${code}. Error: ${errorData}`)
      }
    })
  })
  // endpoint `games`: list of available games for landing page
  .use('/api/games', async (req: any, res: any) => {
    try {
      const games = [];

      // TODO: should be a config file
      const featuredGameNames = [
        {owner: "leanprover-community", game: "nng4"},
        {owner: "hhu-adam", game: "robo"},
        {owner: "alexkontorovich", game: "realanalysisgame"},
        {owner: "djvelleman", game: "stg4"},
        {owner: "trequetrum", game: "lean4game-logic"},
        {owner: "emilyriehl", game: "reintroductiontoproofs"},
        {owner: "jadabouhawili", game: "knightsandknaves-lean4game"},
        {owner: "zrtmrh", game: "linearalgebragame"}
      ]

      // Load featured games
      for (const entry of featuredGameNames) {
        const gameJsonPath = path.join(__dirname, "..", "..", "..", "games", entry.owner, entry.game, ".lake", "gamedata", "game.json")
        let gameJson : any;
          try {
            const raw = await fs.promises.readFile(gameJsonPath, "utf-8");
            gameJson = JSON.parse(raw);
          } catch (err) {
            continue
          }
          games.push({owner: entry.owner, game: entry.game, tile: gameJson.tile})
      }

      // Load local games
      if (isDevelopment){
        const BASE_DIR = path.join(__dirname, "..", "..", "..", "..")
        const entries = await fs.promises.readdir(BASE_DIR, {
          withFileTypes: true,
        });

        for (const entry of entries) {
          if (!entry.isDirectory()) continue;
          const gameJsonPath = path.join(BASE_DIR, entry.name, ".lake", "gamedata", "game.json");
          let gameJson : any;
          try {
            const raw = await fs.promises.readFile(gameJsonPath, "utf-8");
            gameJson = JSON.parse(raw);
          } catch (err) {
            continue
          }
          games.push({owner: "local", game: entry.name, tile: gameJson.tile})
        }
      }

      res.json(games);
    } catch (err) {
      console.error(err);
      res.status(500).json({ error: "Failed to load game tiles" });
    }
  })
  .use('/', router)
  .listen(PORT, () => console.log(`Server listening on ${PORT}`));

const webSocketServer: WebSocketServer = new WebSocketServer({ server });
const observerService = new GameSessionsObserver(gameManager, webSocketServer)
const observer = express()
webSocketServer.addListener("connection", (ws, req) => { observerService.startObservedGame(ws, req) })
//webSocketServer.on("connection", (ws, req) => { observerService.startObservedGame(ws, req) })

/**
 * Start local express instance that provides API for server statistics
 */
observer.use('/api/game-sessions', (req, res) => {
    const measurement = observerService.getAllConnectedPlayers()
    res.status(200).send(measurement)
  })
.listen(API, () => console.log(`API listening on ${API}`));
