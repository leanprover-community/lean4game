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

let router = express.Router();
router.get('/import/status/:owner/:repo', importStatus)
router.get('/import/trigger/:owner/:repo', importTrigger)

const server = app
  .use(express.static(clientDistPath)) // TODO: add a dist folder from inside the game
  .use('/i18n/g/:owner/:repo/:lang/*', (req, res, next) => {
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

    const filename = req.params[0];
    req.url = filename;
    express.static(path.join(gameManager.getGameDir(owner,repo),".i18n",lang))(req, res, next);
  })
  .use('/data/g/:owner/:repo/*', (req, res, next) => {
    const owner = req.params.owner;
    const repo = req.params.repo
    const filename = req.params[0];
    req.url = filename;
    express.static(path.join(gameManager.getGameDir(owner,repo),".lake","gamedata"))(req, res, next);
  })
  .use('/data/stats', (req, res, next) => {
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
        console.error(`stats.sh exited with code ${code}. Error: ${errorData}`)
      }
    })
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
