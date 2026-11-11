import { type ChildProcessWithoutNullStreams, spawn } from 'node:child_process'
import path from 'node:path'

import { isDevMode } from '../utils/devMode.js'

/** Without bubblewrap, commands run directly on the host. */
export const noBwrap = process.env.NO_BWRAP === 'true' || isDevMode()

/**
 * Runs `command` in the game folder, inside the bubblewrap sandbox unless
 * `noBwrap`. The game folder is mounted read-only at `/game`.
 */
export function spawnGame(
  gamePath: string,
  command: string[],
  /** The GameSkeleton doesn't have its own copy of the server and needs leangame as a local dependency */
  includeServerCopy?: boolean,
): ChildProcessWithoutNullStreams {
  if (noBwrap) {
    return spawn(command[0], command.slice(1), { cwd: gamePath })
  }
  const options = [gamePath]
  if (includeServerCopy) {
    const lean4GameFolder = path.join(import.meta.dirname, '..', '..', 'lean')
    options.push('--ro-bind', lean4GameFolder, '/server/lean')
  }
  return spawn(
    // outside `src/`, as the build doesn't copy it to `dist/`
    path.join(import.meta.dirname, '..', '..', 'scripts', 'bubblewrap.sh'),
    [...options, '--', ...command],
  )
}
