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
  const url = artifact.archive_download_url
  progress[id].output += `Download from ${url}\n`
  await download(id, url, `artifact_${artifact.id}.zip`)
  progress[id].output += `Download finished.\n`
  progress[id].output += `Unpacking ZIP.\n`
  const files = await decompress(`artifact_${artifact.id}.zip`, `artifact_${artifact.id}`)
  progress[id].output += `Unpacking TAR.\n`
  const files_inner = await decompress(`artifact_${artifact.id}/${files[0].path}`, `artifact_${artifact.id}_inner`)
  let manifest = fs.readFileSync(`artifact_${artifact.id}_inner/manifest.json`);
  manifest = JSON.parse(manifest);
  if (manifest.length !== 1) {
    throw `Unexpected manifest: ${JSON.stringify(manifest)}`
  }
  manifest[0].RepoTags = [`github-${owner}:${repo}`]
  fs.writeFileSync(`artifact_${artifact.id}_inner/manifest.json`, JSON.stringify(manifest));
  await runProcess(id, "tar", ["-cvf", `../archive_${artifact.id}.tar`, "."], `artifact_${artifact.id}_inner/`)
  await runProcess(id, "docker", ["load", "-i", `archive_${artifact.id}.tar`])
  progress[id].done = true
  progress[id].output += `Done.\n`
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
