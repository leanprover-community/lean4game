import { spawn } from 'child_process'
import fs from 'fs';

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

async function doImport (owner, repo, id) {
  fs.rmSync(`tmp/${owner}/${repo}`, { recursive: true, force: true });
  fs.mkdirSync(`tmp/${owner}/${repo}`, { recursive: true, force: true });
  await runProcess(id, "git", ["clone", `https://github.com/${owner}/${repo}.git`], `tmp/${owner}`)
  await runProcess(id, "docker", ["build", "--rm", "-f", "./Dockerfile", "-t", `github-${owner}:${repo}`, "."], `tmp/${owner}/${repo}`)
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
  res.send(`<html><head><meta http-equiv="refresh" content="2"></head><body><pre>${progress[id]?.output ?? "Nothing here."}</pre></body></html>`)
}
