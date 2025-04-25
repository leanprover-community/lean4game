import fs from 'fs'
import path from 'path'
import util from 'util'
import { exec } from 'child_process'
import { Octokit } from 'octokit'

export { safeImport as default }

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
  const artifacts =  octokit.request('GET /repos/{owner}/{repo}/actions/artifacts', {
    owner,
    repo,
    headers: {
      'X-GitHub-Api-Version': '2022-11-28'
    }
  })

  const artifact = artifacts.data.artifacts.reduce(
    (acc, cur) => acc.created_at < cur.created_at ? cur : acc)

  return artifact.size_in_bytes
}

function safeImport(owner, repo, id, importFunc) {
  return new Promise((resolve, reject) => {
    const rootPath = '/'
    checkDiskSpace(rootPath).then(usedDiskSpace => {
      const artifactMB = getGitHubArtifactInformation(owner, repo) / 1024^2

      if (usedDiskSpace + artifactMB >= RESERVED_DISK_SPACE_MB) {
        return reject(new Error(`[${new Date()}] ABORT IMPORT: Uploading file of size ${artifactMB} (MB) by ${owner} would exceed allocated memory on the server.`))
      }

      importFunc(owner, repo, id)
    })
  })
}
