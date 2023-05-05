import { spawn } from 'child_process'
import fs from 'fs';
import request from 'request'
import requestProgress from 'request-progress'
import { Octokit } from 'octokit';

const TOKEN = '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'
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
  const artifact = artifacts.data.artifacts[0]
  const url = artifact.archive_download_url
  progress[id].output += `Download from ${url}\n`
  await download(id, url, "testfile")
  progress[id].output += `Download finished.\n`
  progress[id].done = true
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
