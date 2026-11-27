import { createJSONStorage } from 'jotai/utils'

export function isDefault<T extends object>(value: T, defValue: T): boolean {
  return (Object.keys(defValue) as (keyof T)[]).every(
    key => value[key] === defValue[key],
  )
}

/**
 * The entries of `defValue`, overwritten by those of `value`. Keys missing in `value`
 * (added later) get their default, keys not in `defValue` (removed since) are dropped.
 */
function withDefaults<T extends object>(value: unknown, defValue: T): T {
  if (typeof value !== 'object' || value === null) return defValue
  const result = { ...defValue }
  for (const key of Object.keys(defValue) as (keyof T)[]) {
    if (key in value) result[key] = (value as T)[key]
  }
  return result
}

/**
 * Only write to local storage if entry has not the default value. Reading fills in
 * missing keys with defaults and drops obsolete keys, so old stored values stay usable.
 */
export function conditionalStorage<T extends object>(defValue: T) {
  const storage = createJSONStorage<T>(() => localStorage)
  return {
    ...storage,
    getItem: (key: string, initialValue: T) =>
      withDefaults(storage.getItem(key, initialValue), defValue),
    setItem: (key: string, value: T) => {
      if (isDefault(value, defValue)) {
        storage.removeItem(key)
      } else {
        storage.setItem(key, value)
      }
    },
  }
}
