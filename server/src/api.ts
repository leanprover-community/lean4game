/*
The types of the data exchanged between server and client. This file is identical in
`server/src/api.ts` and `client/src/api.ts`, check with `npm run api:check`. It must not
import anything.
*/

/** API input to validate a proof */
export interface ApiProofCheckInput {
  world: string
  level: number
  difficulty: number
  inventory: string[]
  tactics: string[]
  /** include hover information for goals and hypotheses */
  hovers?: boolean
  /** the player's language, e.g. `de`, for the anonymous play statistics */
  language?: string
}

/** API result of a proof validation */
export interface ApiProofCheckResult {
  /** the initial state followed by one step per tactic */
  steps: ApiProofStep[]
  /** completed without error or warning */
  completed: boolean
  /** no errors, but warnings present */
  completedWithWarnings: boolean
  hovers: ApiHover[]
  /** Lean docstrings referenced by `hovers` */
  hoverDocs: string[]
}

export type ApiCode =
  | { text: string }
  | { append: ApiCode[] }
  | { tag: [number, ApiCode] }

export interface ApiHover {
  /** type of the subexpression */
  type?: string
  /** the subexpression with implicit arguments */
  expr?: string
  /** index in `hoverDocs` */
  doc?: number
}

export interface ApiProofStep {
  /** the tactic of this step, empty for the initial state */
  tactic: string
  /** the goals after this step */
  goals: ApiGoal[]
  diagnostics: ApiDiagnostic[]
}

export interface ApiGoal {
  userName?: string
  hyps: ApiHypothesis[]
  type: string
  hints: ApiHint[]
  /** `type` with hover information */
  typeWithHover?: ApiCode
}

export interface ApiHypothesis {
  names: string[]
  type: string
  /** value of a `let` variable */
  value?: string
  /** the hypothesis is of type `Prop` */
  isAssumption: boolean
  /** `type` with hover information */
  typeWithHover?: ApiCode
  /** `value` with hover information */
  valueWithHover?: ApiCode
}

export interface ApiHint {
  text: string
  hidden: boolean
  rawText: string
  varNames: [string, string][]
}

export interface ApiDiagnostic {
  /** 1: error, 2: warning, 3: information, 4: hint */
  severity: number
  message: string
  /** 0-based line relative to the first tactic */
  line: number
  character: number
}

/** A game to be displayed on the landing page */
export interface ApiGameInfo {
  owner: string
  repo: string
  /** listed in the `featuredGames` of the server config */
  featured: boolean
  /** `tile` and `settings` of the game's `game.json` */
  tile: ApiGameTile | null
  settings: ApiGameSettings | null
}

/** The `tile` of a game's `game.json`, shown on the landing page */
export interface ApiGameTile {
  title: string
  short: string
  long: string
  prerequisites: string[]
  worlds: number
  levels: number
  languages: string[]
  image?: string
}

/** The `settings` of a game's `game.json` */
export interface ApiGameSettings {
  /** an empty translation hides a text instead of showing the original */
  allowEmptyTranslations?: boolean
}

/** A game's `game.json`, see `/api/data/:owner/:game/game` */
export interface ApiGameData {
  title: null | string
  introduction: null | string
  info: null | string
  worlds: null | {
    nodes: {
      [id: string]: {
        id: string
        title: string
        introduction: string
        conclusion?: string
        image: string
      }
    }
    edges: string[][]
  }
  worldSize: null | { [key: string]: number }
  authors: null | string[]
  conclusion: null | string
  tile: null | ApiGameTile
  image: null | string
  settings?: null | ApiGameSettings
}

export interface ApiInventoryTile {
  name: string
  displayName: string
  category: string
  disabled: boolean
  locked: boolean
  new: boolean
  hidden: boolean
  altTitle: string
  world: string | null
  level: number | null
  proven: boolean
}

/** A level, see `/api/data/:owner/:game/level/:world/:level` */
export interface ApiLevelData {
  title: null | string
  introduction: null | string
  conclusion: null | string
  index: number
  tactics: ApiInventoryTile[]
  theorems: ApiInventoryTile[]
  definitions: ApiInventoryTile[]
  descrText: null | string
  descrFormat: null | string
  theoremTab: null | string
  statementName: null | string
  displayName: null | string
  template: null | string
  image: null | string
}

/** The inventory shown on a game's welcome page, see `/api/data/:owner/:game/inventory` */
export interface ApiInventoryOverview {
  tactics: ApiInventoryTile[]
  theorems: ApiInventoryTile[]
  definitions: ApiInventoryTile[]
  theoremTab: null | string
}

/** Documentation of a tactic, theorem or definition, see `/api/data/:owner/:game/doc/:kind/:name` */
export interface ApiDoc {
  name: string
  displayName: string
  content: string
  statement: string
  type: string
  category: string
  /** the levels introducing the item, missing in games built before this was added */
  introducedIn?: { world: string; level: number }[]
  /** the link to the mathlib documentation, if the declaration is documented there */
  mathlibDoc?: string | null
}

/**
 * Text which may differ per language, either one string for all languages or e.g.
 * `{ "en": "Germany", "de": "Deutschland" }`. Missing languages fall back to `en`.
 */
export type ApiLocalized = string | Partial<Record<string, string>>

export interface ApiAnnouncement {
  title: ApiLocalized
  /** in Markdown */
  message: ApiLocalized
}

/** The part of the config which the client gets from `/api/config` */
export interface ApiClientConfig {
  /** Shown at the top of the landing page */
  announcements: ApiAnnouncement[]
  /** The responsible persons, shown in the impressum and the privacy policy */
  contact?: {
    name: string
    /** One entry per line */
    address: ApiLocalized[]
    phone?: string
    /** Link to further contact details */
    url?: string
    /** Email address for technical questions */
    technicalEmail?: string
  }
  impressum?: {
    /** e.g. the legal form, representation and supervisory authority of the operator */
    legalForm?: ApiLocalized
    /** VAT identification number according to §27a UStG */
    vatId?: string
    /** Link to the impressum of the operating institution */
    link?: { label: ApiLocalized; url: string }
  }
  privacy?: {
    /** Country where the server is located */
    serverLocation?: ApiLocalized
  }
}

/** The status of the import of a game */
export interface ApiImportStatus {
  state: 'running' | 'done' | 'failed'
  startedAt: string
  /** output of the import steps */
  log: string[]
  /** problems which don't stop the import, e.g. an incompletely built game */
  warnings: string[]
  /** progress of the artifact download, updated while downloading */
  download?: { receivedBytes: number; totalBytes: number }
}

/** Statistic about a game's import history */
export interface ApiGameImportStats {
  owner: string
  repo: string
  /** from `lean-toolchain`, e.g. `leanprover/lean4:v4.23.0` */
  toolchain: string | null
  /** e.g. `v4.23.0` */
  leanVersion: string | null
  /** `null` for games imported before the import history was recorded */
  firstImportedAt: string | null
  lastImportedAt: string | null
  importCount: number
  /** e.g. `"2026-10-18"` → 2 */
  importsPerDay: Record<string, number>
  /** whether the last import was fully built */
  fullyBuilt: boolean | null
}

/** How busy the server is, as shares between `0.0` and `1.0` */
export interface ApiServerLoad {
  /** used memory, memory the system can reclaim counts as available */
  memory: number
  /** CPU usage over the last few seconds, over all cores */
  cpu: number
}

/** Number of Lean instances of a game which have not exited */
export interface ApiGameInstanceCount {
  owner: string
  repo: string
  count: number
}

/** Anonymous play statistics of a game in one 30-minute interval */
export interface ApiGameActivityStats {
  /** start of the interval, UTC, e.g. `"2026-10-22T14:30Z"` */
  interval: string
  owner: string
  repo: string
  /** the language the game is played in, e.g. `de`, or `unknown` */
  language: string
  /** first language of the browser's `Accept-Language`, e.g. `fr`, or `unknown` */
  preferredLanguage: string
  /** players whose first check fell into this interval */
  sessions: number
  checks: number
  /** active play time, without breaks */
  playSeconds: number
}
