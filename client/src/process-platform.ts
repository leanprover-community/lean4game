/**
 * The `process` polyfill from `vite-plugin-node-polyfills` has no `platform`.
 * The VS Code libraries behind the editor pick their path implementation from
 * `process.platform`, but detect Windows from the user agent when building file
 * paths. On Windows this mix makes every editor file write fail (#445, #451).
 *
 * Fill in `platform` the way VS Code does when no `process` exists. This module
 * must be imported before anything that loads the editor.
 */
if (typeof process !== 'undefined' && !process.platform) {
  const userAgent = navigator.userAgent
  ;(process as { platform: string }).platform =
    userAgent.includes('Windows') ? 'win32' :
    userAgent.includes('Macintosh') ? 'darwin' :
    'linux'
}

export {}
