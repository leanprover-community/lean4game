/*
 * Start with `pm2 start ecosystem.config.cjs` from the repository root
 * after `npm run build`.
 * See `doc/server/server.md` for all environment variables.
 */

const path = require('node:path')

module.exports = {
  apps: [
    {
      name: 'leangame',
      script: path.join(__dirname, 'server', 'dist', 'index.js'),
      cwd: path.join(__dirname, 'server'),
      env: {
        NODE_ENV: 'production',
        PORT: 8000,
        // only reachable through nginx, see `deploy/nginx/leangame.conf`
        HOST: '127.0.0.1',
        LEANGAME_GITHUB_TOKEN: '',
        LEANGAME_GITHUB_USER: '',
      },
    },
  ],
}
