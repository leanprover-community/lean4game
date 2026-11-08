/** An error answer of the server, e.g. `status` 404 */
export class HttpError extends Error {
  status: number
  /** How long to wait after a `status` 429 */
  retryAfterSeconds: number
  constructor(url: string, res: Response) {
    super(`${url}: ${res.status} ${res.statusText}`)
    this.status = res.status
    this.retryAfterSeconds = Number(res.headers.get('Retry-After'))
  }
}

/** The parsed json of `url`, throws an `HttpError` if the server answers with an error */
export async function fetchJson<T>(url: string): Promise<T> {
  const res = await fetch(url)
  if (!res.ok) throw new HttpError(url, res)
  return res.json() as Promise<T>
}

/** The URL of the game data `path` of the game `gameId`, which is `g/owner/repo` */
export function gameDataUrl(gameId: string, path: string): string {
  return `/api/data/${gameId.replace(/^g\//, '')}/${path}`
}

/** `retry` for queries: up to 3 times, but not if the server answered e.g. 404 */
export function retryUnlessClientError(failureCount: number, error: Error) {
  if (error instanceof HttpError && error.status >= 400 && error.status < 500)
    return false
  return failureCount < 3
}

/** POSTs `body` as json to `url`, throws an `HttpError` if the server answers with an error */
export async function postJson<T>(url: string, body?: unknown): Promise<T> {
  const res = await fetch(url, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body ?? {}),
  })
  if (!res.ok) throw new HttpError(url, res)
  return res.json() as Promise<T>
}
