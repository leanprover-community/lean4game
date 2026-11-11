import { existsSync } from 'node:fs'
import path from 'node:path'

import express, { type Express } from 'express'

/*
In production, the server also serves the built client (`npm run build` writes it to
`client/dist`). In development, Vite serves the client instead.
*/

const CLIENT_DIR = path.resolve(
  import.meta.dirname,
  '..',
  '..',
  'client',
  'dist',
)

/** Paths handled by the server itself, which never fall back to the client */
const SERVER_PATHS = /^\/(api|stats|ping)(\/|$)/

/** The client's pages of games, `/g/owner/repo/...` */
const GAME_PATHS = /^\/g\//

/** Serves the built client. Must be called after all other routes. */
export function serveClient(app: Express) {
  if (!existsSync(CLIENT_DIR)) {
    console.warn(`No built client in ${CLIENT_DIR}, run \`npm run build\``)
  }

  app.use(
    express.static(CLIENT_DIR, {
      index: false,
      setHeaders: (res, filePath) => {
        // Vite puts a hash into the names of the built files, so they never change
        if (filePath.startsWith(path.join(CLIENT_DIR, 'assets') + path.sep)) {
          res.setHeader('Cache-Control', 'public, max-age=31536000, immutable')
        }
      },
    }),
  )

  // `index.html` for all other pages, so that reloading a page of the client works. It is
  // never cached, so a new build is picked up immediately. Missing files, e.g. assets of an
  // older build, get a 404 instead. Game pages `/g/...` may contain dots, e.g. in the
  // repository's name, so they are never files.
  app.get(/.*/, (req, res, next) => {
    if (SERVER_PATHS.test(req.path)) return next()
    if (!GAME_PATHS.test(req.path) && path.extname(req.path)) return next()
    res.setHeader('Cache-Control', 'no-cache')
    res.sendFile(path.join(CLIENT_DIR, 'index.html'))
  })
}
