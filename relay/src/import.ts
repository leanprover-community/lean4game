import fs from 'fs';
import got from 'got'
import path from 'path';
import { Octokit } from 'octokit';
import { spawn } from 'child_process'
import { pipeline } from 'node:stream/promises'
import { fileURLToPath } from 'url';
import { gameActivityStore } from './services/GameActivityStore.js';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const TOKEN = process.env.LEAN4GAME_GITHUB_TOKEN
const USERNAME = process.env.LEAN4GAME_GITHUB_USER
const CONTACT = process.env.ISSUE_CONTACT || 'https://github.com/leanprover-community/lean4game/issues'

const octokit = new Octokit({
  auth: TOKEN
})

const progress = {}

async function runProcess(id, cmd, args, cwd) {
  return new Promise<void>((resolve, reject) => {
    const ls = spawn(cmd, args, {cwd});
    ls.on('error', reject);

    ls.stdout.on('data', (data) => {
      progress[id].output += data.toString()
    });

    ls.stderr.on('data', (data) => {
      progress[id].output += data.toString()
    });

    ls.on('close', (code) => {
      if (code === 0) resolve()
      else reject(new Error(cmd + " exited with code " + code))
    });
  })
}

async function download(id, url, dest) {
  let numProgressChars = 0
  progress[id].output += "Progress: " + "[" + "_".repeat(50) + "]"
  const source = got.stream.get(url, {
    // Stop stalled transfers; active downloads can take longer than a minute.
    timeout: { socket: 60_000 },
    headers: {
      'accept': 'application/vnd.github+json',
      'User-Agent': USERNAME,
      'X-GitHub-Api-Version': '2022-11-28',
      'Authorization': 'Bearer ' + TOKEN
    }
  }).on('downloadProgress', downloadProgress => {
    let step = Math.round((downloadProgress.percent * 100) / 2);
    if (step > numProgressChars && downloadProgress.transferred != 0) {
      progress[id].output = progress[id].output.replace(/\[[#_]*\]/, `[${'#'.repeat(numProgressChars) + "_".repeat(50 - numProgressChars)}] `)
      numProgressChars = step
    }
  })
  // Finish writing the file before unpacking it.
  await pipeline(source, fs.createWriteStream(dest))
  progress[id].output += "\n"
}

async function doImport (owner, repo, id) {
  progress[id].output += `Import starting in a few seconds...\n`
  await new Promise(resolve => setTimeout(resolve, 3000))
  let artifactId = null
  let artifactPath: string
  const gamesPath = path.join(__dirname, "..", "..", "..", "games");
  const gamesTmpPath = path.join(gamesPath, "tmp");
  // Let the trigger report failures; cleanup still runs in finally.
  try {
    const artifacts = await octokit.request('GET /repos/{owner}/{repo}/actions/artifacts', {
      owner,
      repo,
      headers: {
        'X-GitHub-Api-Version': '2022-11-28'
      }
    })
    const artifact = artifacts.data.artifacts
      .reduce((acc, cur) => acc.created_at < cur.created_at ? cur : acc)

    artifactId = artifact.id
    artifactPath = path.join(gamesTmpPath, `${owner.toLowerCase()}_${repo.toLowerCase()}_${artifactId}`)
    const url = artifact.archive_download_url
    const unpackingScript = path.join(__dirname, "..", "..", "scripts", "unpack.sh")
    const toolchainScript = path.join(__dirname, "..", "..", "scripts", "install_toolchain.sh")

    // Make sure the download folder exists
    if (!fs.existsSync(gamesPath)){
      fs.mkdirSync(gamesPath);
    }
    if (!fs.existsSync(gamesTmpPath)){
      fs.mkdirSync(gamesTmpPath);
    }
    progress[id].output += `Download from ${url}\n`
    await download(id, url, `${artifactPath}.zip`)
    progress[id].output += `Download finished.\n`

    // Unpack downloaded game
    await runProcess(id, "/bin/bash", [unpackingScript, gamesPath, artifactId, owner.toLowerCase(), repo.toLowerCase()], path.join(__dirname, "..", ".."))
    // Install necessary toolchain
    await runProcess(id, "/bin/bash", [toolchainScript, gamesPath, owner.toLowerCase(), repo.toLowerCase()], path.join(__dirname, "..", ".."))

    const gameJsonPath = path.join(
      gamesPath, owner.toLowerCase(), repo.toLowerCase(), ".lake", "gamedata", "game.json"
    )
    if (!fs.existsSync(gameJsonPath)) {
      throw new Error("Imported artifact does not contain " + gameJsonPath)
    }
    await gameActivityStore.recordImport(owner, repo)
    progress[id].output += `Activity registry updated.\n`


    // let manifest = fs.readFileSync(`tmp/artifact_${artifactId}_inner/manifest.json`);
    // manifest = JSON.parse(manifest);
    // if (manifest.length !== 1) {
    //   throw `Unexpected manifest: ${JSON.status(manifest)}`
    // }
    // manifest[0].RepoTags = [`g/${owner.toLowerCase()}/${repo.toLowerCase()}:latest`]
    // fs.writeFileSync(`tmp/artifact_${artifactId}_inner/manifest.json`, JSON.stringify(manifest));
    // await runProcess(id, "tar", ["-cvf", `../archive_${artifactId}.tar`, "."], `tmp/artifact_${artifactId}_inner/`)
    // // await runProcess(id, "docker", ["load", "-i", `tmp/archive_${artifactId}.tar`])



    progress[id].done = true
    progress[id].output += `Done!\n`
    const gameUrl = `/#/g/${owner}/${repo}`
    progress[id].output += `Play the game at: <a href="${gameUrl}">${gameUrl}</a>\n`
  } finally {
    // Use the download path to remove partial ZIPs and failed extractions too.
    if (artifactPath) {
      fs.rmSync(`${artifactPath}.zip`, {force: true, recursive: false});
      fs.rmSync(artifactPath, {force: true, recursive: true});
      fs.rmSync(`${artifactPath}_game`, {force: true, recursive: true});
    }
    progress[id].done = true
  }
  await new Promise(resolve => setTimeout(resolve, 10000))
}

export const importTrigger = (req, res) => {
  const owner = req.params.owner
  const repo = req.params.repo
  const id = req.params.owner + '/' + req.params.repo
  if(!/^[\w.-]+\/[\w.-]+$/.test(id)) { res.send(`Invalid repo name ${id}`); return }

  if(!progress[id] || progress[id].done) {
    progress[id] = {output: "", done: false}
    doImport(owner, repo, id)
    .catch((err: Error) => {
      const message = err.toString().replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
      progress[id].output += `${message}\n
      Please <a href="${CONTACT}">report this issue</a> and include the error above.`
      // A failed attempt must not block the next trigger.
      progress[id].done = true
      console.error(err)
    })
  }

  res.redirect(`/import/status/${owner}/${repo}`)
}

export const importStatus = (req, res) => {
  const owner = req.params.owner
  const repo = req.params.repo
  const id = req.params.owner + '/' + req.params.repo
  res.send(`<html><head><meta http-equiv="refresh" content="5"></head><body><pre>${progress[id]?.output ?? "Nothing here."}</pre></body></html>`)
}
