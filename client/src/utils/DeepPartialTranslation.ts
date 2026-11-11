export type DeepPartialTranslation<T> = {
  [K in keyof T]?: T[K] extends object ? DeepPartialTranslation<T[K]> : string
}
