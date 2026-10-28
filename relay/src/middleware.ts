import fs from 'fs'
import anonymize from 'ip-anonymize'
import path from 'path'
import process from 'process'
import { AccessLogger, Connection } from './services/AccessLogger.js'
import { Request, Response } from 'express'

const accessLogger = new AccessLogger()

export function logConnection(req: Request, res: Response): void {
  accessLogger.logConnections(req, res)
}

export function getActiveConnections(): Connection[] {
  return accessLogger.getActiveConnections()
}

export function logGameAccess(req) {
  const owner = req.params.owner;
  const repo = req.params.repo;
  const lang = req.params.lang;

  const anon_ip = anonymize(req.headers['x-forwarded-for'] || req.socket.remoteAddress);
  const log = path.join(process.cwd(), 'logs', 'game-access.log');
  const header = "date;anon-ip;game;lang\n";
  const data = `${new Date()};${anon_ip};${owner}/${repo};${lang}\n`;

  fs.mkdir(path.join(process.cwd(), 'logs'), { recursive: true }, (err) => {
    if (err) console.log("Failed to create logs directory!");
    else {
      // 'ax' fails if the file already exists: https://nodejs.org/api/fs.html#file-system-flags
      fs.writeFile(log, header.concat(data), { flag: 'ax' }, (file_exists) => {
        if (file_exists) {
          fs.appendFile(log, data, (err) => {
            if (err) console.log(`Failed to append to log: ${err}`);
          });
        }
      });
    }
  });

  console.log(`[${new Date()}] ${anon_ip} requested translation for ${owner}/${repo} in ${lang}`);
  return { owner, repo, lang };
}
