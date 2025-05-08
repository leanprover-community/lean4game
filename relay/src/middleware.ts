import { exec } from 'child_process'
import { Octokit } from 'octokit'
import { UAParser } from 'ua-parser-js';
import fs from 'fs';
import anonymize from 'ip-anonymize';
import path from 'path'
import crypto from 'crypto'


const TOKEN = process.env.LEAN4GAME_GITHUB_TOKEN
const RESERVED_DISK_SPACE_MB: number = parseInt(process.env.RESERVED_DISC_SPACE_MB)
const DISK_INFO_CMD_MB = 'df -BM'
const octokit = new Octokit({auth: TOKEN})

function checkDiskSpace(path) {
  return new Promise<number>((resolve, reject) => {
    exec(DISK_INFO_CMD_MB, path, (error, stdout, stderr) => {
      if (error) {
        return reject(new Error(`Error checking disk space: ${error.message}`))
      }

      const lines = stdout.toString().trim().split('\n')
      if (lines.length < 2){
        return reject(new Error(`Invalid disk information output`))
      }

      const stats = lines[1].split(/\s+/)
      const usedDiskSpace = parseInt(stats[3].replace('M', ''))

      resolve(usedDiskSpace)
    })
  })
}

function getGitHubArtifactInformation(owner, repo){
  return new Promise<number>(async (resolve, reject) =>{
    const artifacts =  octokit.request('GET /repos/{owner}/{repo}/actions/artifacts', {
      owner,
      repo,
      headers: {
        'X-GitHub-Api-Version': '2022-11-28'
      }
    })

    const artifact = (await artifacts).data.artifacts.reduce(
      (acc, cur) => acc.created_at < cur.created_at ? cur : acc)

    resolve(artifact.size_in_bytes)
  })
}

function generateFingerprint(req): string {
  const signals: Array<string> = []

  const ip = req.headers['x-forwarded-for'] || req.socket.remoteAddress
  const acceptLanguage = req.headers['accept-language'] || "unknown-language"
  const width = req.headers['sec-ch-viewport-width'] || 'unknonwn-width';
  const height = req.headers['sec-ch-viewport-height'] || 'unknown-height';
  const dpr = req.headers['sec-ch-device-pixel-ratio'] || 'unknown-dpr'
  const platform = req.headers['sec-ch-ua-platform'] || 'unknown-platform';
  const mobile = req.headers['sec-ch-ua-mobile'] || 'unknown-mobile';
  const model = req.headers['sec-ch-ua-model'] || 'unknown-model';

  // Parse user agent for additional signals
  const parser = new UAParser(req.headers['user-agent'] || "")
  const browserName: string = parser.getBrowser().name || "unknown-browser-name"
  const browserVersion: string = parser.getBrowser().version || "unknown-browser-version"
  const browserMajor: string = parser.getBrowser().major || "unknown-browser-major"
  const browsertype: string = parser.getBrowser().type || "unknown-browser-type"
  const osName: string = parser.getOS().name || "unknown-os-name"
  const osVersion: string = parser.getOS().version || "unknown-os-version"
  const deviceModel: string = parser.getDevice().model || "unknown-device-model"
  const deviceType: string = parser.getDevice().type || "unknown-device-type"
  const deviceVendor: string = parser.getDevice().vendor || "unknown-device-vendor"



  signals.push(
    ip,
    acceptLanguage,
    width,
    height,
    dpr,
    platform,
    mobile,
    model,
    browserName,
    browserVersion,
    browserMajor,
    browsertype,
    osName,
    osVersion,
    deviceModel,
    deviceType,
    deviceVendor)

  console.log(signals.join('+'))
  return crypto.createHash('sha256').update(signals.join('+')).digest('hex')
}

export function logAccess(req) {
  const owner = req.params.owner;
  const repo = req.params.repo;
  const lang = req.params.lang;

  const fingerprint: string = generateFingerprint(req)

  const anon_ip = anonymize(req.headers['x-forwarded-for'] || req.socket.remoteAddress);
  const log = path.join(process.cwd(), 'logs', 'game-access.log');
  const header = "date;anon-ip;fingerprint;game;lang\n";
  const data = `${new Date()};${anon_ip};${fingerprint};${owner}/${repo};${lang}\n`;

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


export function safeImport(owner, repo, id, importFunc) {
  return new Promise<void>((resolve, reject) => {
    const rootPath = '/'
    checkDiskSpace(rootPath).then(async usedDiskSpace => {
      const artifactByte = await getGitHubArtifactInformation(owner, repo)
      const artifactMB = Math.ceil(artifactByte / Math.pow(1024, 2))

      if (usedDiskSpace + artifactMB >= RESERVED_DISK_SPACE_MB) {
        return reject(new Error(`[${new Date()}] ABORT IMPORT: Uploading file of size ${artifactMB} (MB) by ${owner} would exceed allocated memory of ${RESERVED_DISK_SPACE_MB} on the server.`))
      }

      importFunc(owner, repo, id)
      return resolve(console.log(`[${new Date()}] ${owner} uploaded file of size ${artifactMB} (MB).
      Remaining reserved memory amounts to ${RESERVED_DISK_SPACE_MB - usedDiskSpace + artifactMB} (MB)`))
    })
  })
}
