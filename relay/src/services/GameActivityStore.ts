import fs from 'fs'
import path from 'path'

export interface GameActivity {
  firstSeenAt: string
  firstImportedAt: string | null
  lastImportedAt: string | null
  lastPlayedAt: string | null
}

export type GameActivityRegistry = Record<string, GameActivity>

/** Persist import and real-play timestamps without storing player identities. */
export class GameActivityStore {
  private readonly filePath: string
  private pendingWrite: Promise<void> = Promise.resolve()

  constructor(filePath: string) {
    this.filePath = filePath
  }

  getPath(): string {
    return this.filePath
  }

  async getAll(): Promise<GameActivityRegistry> {
    await this.pendingWrite
    return this.read()
  }

  recordImport(owner: string, repo: string, now: Date = new Date()): Promise<void> {
    return this.update(owner, repo, 'import', now)
  }

  recordPlay(owner: string, repo: string, now: Date = new Date()): Promise<void> {
    return this.update(owner, repo, 'play', now)
  }

  recordSeen(owner: string, repo: string, now: Date = new Date()): Promise<void> {
    return this.update(owner, repo, 'seen', now)
  }

  private update(owner: string, repo: string, event: 'import' | 'play' | 'seen', now: Date): Promise<void> {
    const key = `${owner.toLowerCase()}/${repo.toLowerCase()}`
    const timestamp = now.toISOString()

    const operation = this.pendingWrite.then(async () => {
      const registry = await this.read()
      const activity: GameActivity = registry[key] ?? {
        firstSeenAt: timestamp,
        firstImportedAt: null,
        lastImportedAt: null,
        lastPlayedAt: null,
      }

      if (event === 'import') {
        activity.firstImportedAt ??= timestamp
        activity.lastImportedAt = timestamp
      } else if (event === 'play') {
        activity.lastPlayedAt = timestamp
      }
      registry[key] = activity

      await this.write(registry)
    })

    // A failed write must not permanently poison the serialization queue.
    this.pendingWrite = operation.catch(() => undefined)
    return operation
  }

  private async read(): Promise<GameActivityRegistry> {
    try {
      const raw = await fs.promises.readFile(this.filePath, 'utf8')
      const registry = JSON.parse(raw) as GameActivityRegistry
      for (const activity of Object.values(registry)) {
        delete (activity as any).status
        delete (activity as any).inactiveSince
      }
      return registry
    } catch (error: any) {
      if (error?.code === 'ENOENT') return {}
      throw error
    }
  }

  private async write(registry: GameActivityRegistry): Promise<void> {
    const directory = path.dirname(this.filePath)
    const temporaryPath = `${this.filePath}.${process.pid}.tmp`
    await fs.promises.mkdir(directory, { recursive: true })
    await fs.promises.writeFile(temporaryPath, `${JSON.stringify(registry, null, 2)}\n`, 'utf8')
    await fs.promises.rename(temporaryPath, this.filePath)
  }
}

const defaultActivityPath = path.join(process.cwd(), 'games', '.lean4game', 'activity.json')

export const gameActivityStore = new GameActivityStore(
  process.env.GAME_ACTIVITY_FILE || defaultActivityPath
)
