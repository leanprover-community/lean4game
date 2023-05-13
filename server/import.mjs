import { spawn } from 'child_process'
import fs from 'fs';
import request from 'request'
import decompress from 'decompress'
import requestProgress from 'request-progress'
import { Octokit } from 'octokit';

const TOKEN = process.env.LEAN4GAME_GITHUB_TOKEN
const octokit = new Octokit({
  auth: TOKEN
})

const progress = {}

async function runProcess(id, cmd, args, cwd) {
  return new Promise((resolve, reject) => {
    const ls = spawn(cmd, args, {cwd});

    ls.stdout.on('data', (data) => {
      progress[id].output += data.toString()
    });

    ls.stderr.on('data', (data) => {
      progress[id].output += data.toString()
    });

    ls.on('close', (code) => {
      resolve()
    });
  })
}

async function download(id, url, dest) {
  return new Promise((resolve, reject) => {
    // The options argument is optional so you can omit it
    requestProgress(request({
      url,
      headers: {
        'User-Agent': 'abentkamp',
        'X-GitHub-Api-Version': '2022-11-28',
        'Authorization': 'Bearer '+TOKEN
      }
    }))
    .on('progress', function (state) {
      progress[id].output += `Downloaded ${Math.round(state.size.transferred/1024/1024)}MB\n`
    })
    .on('error', function (err) {
      reject(err)
    })
    .on('end', function () {
      resolve()
    })
    .pipe(fs.createWriteStream(dest));
  })
}

async function doImport (owner, repo, id) {
  progress[id].output += `Import starting in a few seconds...\n`
  await new Promise(resolve => setTimeout(resolve, 3000))
  let artifactId = null
  try {
    const artifacts = await octokit.request('GET /repos/{owner}/{repo}/actions/artifacts', {
      owner,
      repo,
      headers: {
        'X-GitHub-Api-Version': '2022-11-28'
      }
    })
    // choose latest artifact
    const artifact = artifacts.data.artifacts
      .reduce((acc, cur) => acc.created_at < cur.created_at ? cur : acc)
    artifactId = artifact.id
    const url = artifact.archive_download_url
    if (!fs.existsSync("tmp")){
      fs.mkdirSync("tmp");
    }
    progress[id].output += `Download from ${url}\n`
    await download(id, url, `tmp/artifact_${artifactId}.zip`)
    progress[id].output += `Download finished.\n`
    progress[id].output += `Unpacking ZIP.\n`
    const files = await decompress(`tmp/artifact_${artifactId}.zip`, `tmp/artifact_${artifactId}`)
    if (files.length != 1) { throw Error(`Unexpected number of files in ZIP: ${files.length}`) }
    progress[id].output += `Unpacking TAR.\n`
    const files_inner = await decompress(`tmp/artifact_${artifactId}/${files[0].path}`, `tmp/artifact_${artifactId}_inner`)
    let manifest = fs.readFileSync(`tmp/artifact_${artifactId}_inner/manifest.json`);
    manifest = JSON.parse(manifest);
    if (manifest.length !== 1) {
      throw `Unexpected manifest: ${JSON.stringify(manifest)}`
    }
    manifest[0].RepoTags = [`github-${owner?.toString().toLowerCase()}:${repo}`]
    fs.writeFileSync(`tmp/artifact_${artifactId}_inner/manifest.json`, JSON.stringify(manifest));
    await runProcess(id, "tar", ["-cvf", `../archive_${artifactId}.tar`, "."], `tmp/artifact_${artifactId}_inner/`)
    await runProcess(id, "docker", ["load", "-i", `tmp/archive_${artifactId}.tar`])
    progress[id].done = true
    progress[id].output += `Done.\n`
  } catch (e) {
    progress[id].output += `Error: ${e.toString()}\n${e.stack}`
  } finally {
    if (artifactId) {
      fs.rmSync(`tmp/artifact_${artifactId}.zip`, {force: true, recursive: true});
      fs.rmSync(`tmp/artifact_${artifactId}`, {force: true, recursive: true});
      fs.rmSync(`tmp/artifact_${artifactId}_inner`, {force: true, recursive: true});
      fs.rmSync(`tmp/archive_${artifactId}.tar`, {force: true, recursive: true});
    }
    progress[id].done = true
  }
}

export const importTrigger = (req, res) => {
  const owner = req.params.owner
  const repo = req.params.repo
  const id = req.params.owner + '/' + req.params.repo
  if(!/^[\w.-]+\/[\w.-]+$/.test(id)) { res.send(`Invalid repo name ${id}`); return }

  if(!progress[id] || progress[id].done) {
    progress[id] = {output: "", done: false}
    doImport(owner, repo, id)
  }

  res.redirect(`/import/status/${owner}/${repo}`)
}

export const importStatus = (req, res) => {
  const owner = req.params.owner
  const repo = req.params.repo
  const id = req.params.owner + '/' + req.params.repo
  res.send(`<html><head><meta http-equiv="refresh" content="5"></head><body><pre>${progress[id]?.output ?? "Nothing here."}</pre></body></html>`)
}
