/// <reference types="vite/client" />

interface ImportMetaEnv {
  readonly VITE_LEAN4GAME_SINGLE: string
  // more env variables...
}

interface ImportMeta {
  readonly env: ImportMetaEnv
}
