/**
 * Compares the translations of the interface with `en.ts` and the code, see `doc/client/translation-interface.md`:
 *
 *   npm run i18n:check        a summary of all languages
 *   npm run i18n:check -- es  also lists the keys missing in `es`
 *
 * Fails on superfluous and unused keys, but not on missing ones, as these fall back to
 * English. Runs on Node's type stripping, so `translations/` may only import types.
 */
import { readdirSync, readFileSync } from 'node:fs'
import { join, sep } from 'node:path'
import { pathToFileURL } from 'node:url'

type Translation = { [key: string]: string | Translation }

const SRC = join(import.meta.dirname, '..', 'src')
const TRANSLATIONS = join(SRC, 'translations')

/** All keys of a translation in the form `appBar.start` */
function flatKeys(translation: Translation, prefix = ''): string[] {
  return Object.entries(translation).flatMap(([key, value]) =>
    typeof value === 'string'
      ? [prefix + key]
      : flatKeys(value, `${prefix}${key}.`),
  )
}

/** The keys of the translation file of the language `iso` */
async function loadKeys(iso: string): Promise<string[]> {
  const file = pathToFileURL(join(TRANSLATIONS, `${iso}.ts`)).href
  const module = (await import(file)) as Record<string, Translation>
  // each file has one export, e.g. `ptBR` in `pt-BR.ts`
  return flatKeys(Object.values(module)[0])
}

/** The contents of all source files, except for the translations themselves */
function readSources(): string[] {
  return readdirSync(SRC, { recursive: true, encoding: 'utf8' })
    .filter(
      file => /\.tsx?$/.test(file) && !file.startsWith(`translations${sep}`),
    )
    .map(file => readFileSync(join(SRC, file), 'utf8'))
}

/**
 * Patterns for keys built at runtime, e.g. `gameInfo.${section}.title`. Only templates
 * starting with a key prefix count, as e.g. `${name}` would match any key.
 */
function dynamicKeyPatterns(sources: string[]): RegExp[] {
  return sources.flatMap(source =>
    [...source.matchAll(/`(\w+\.[\w.]*\$\{[^`]*)`/g)].map(([, template]) => {
      const pattern = template
        .split(/\$\{[^}]*\}/)
        .map(text => text.replaceAll('.', String.raw`\.`))
        .join(String.raw`[^.]+`)
      return new RegExp(`^${pattern}$`)
    }),
  )
}

/**
 * The keys of `keys` which the code mentions nowhere. A key with a suffix of i18next,
 * e.g. the context in `masks.name_raw` or the plural in `levels_one`, counts as used if
 * the key without it is, e.g. in `t('masks.name', { context: mask })`.
 */
function findUnused(keys: string[]): string[] {
  const sources = readSources()
  const patterns = dynamicKeyPatterns(sources)
  const isMentioned = (key: string) =>
    patterns.some(pattern => pattern.test(key)) ||
    sources.some(source =>
      ["'", '"', '`'].some(quote => source.includes(`${quote}${key}${quote}`)),
    )
  return keys.filter(
    key => !isMentioned(key) && !isMentioned(key.replace(/_[^.]*$/, '')),
  )
}

function printList(title: string, keys: string[]) {
  if (keys.length === 0) return
  console.log(`\n${title}:`)
  for (const key of keys) console.log(`  ${key}`)
}

const config = JSON.parse(readFileSync(join(SRC, 'config.json'), 'utf8')) as {
  languages: { iso: string }[]
}
const languages = config.languages
  .map(({ iso }) => iso)
  .filter(iso => iso !== 'en')

const detailed = process.argv.at(2)
if (detailed != null && !languages.includes(detailed)) {
  console.error(
    `Unknown language '${detailed}', use one of: ${languages.join(', ')}`,
  )
  process.exit(2)
}

const enKeys = await loadKeys('en')
const superfluous: string[] = []
let missingInDetailed: string[] = []

console.log(`Missing translations (of ${enKeys.length} keys):`)
for (const iso of languages) {
  const keys = await loadKeys(iso)
  const missing = enKeys.filter(key => !keys.includes(key))
  console.log(`  ${iso.padEnd(6)}${String(missing.length).padStart(4)}`)
  superfluous.push(
    ...keys.filter(key => !enKeys.includes(key)).map(key => `${iso}: ${key}`),
  )
  if (iso === detailed) missingInDetailed = missing
}

const unused = findUnused(enKeys)
printList(`Missing in ${detailed}`, missingInDetailed)
printList('Superfluous keys, not in en.ts', superfluous)
printList('Unused keys, in en.ts but not in the code', unused)

if (superfluous.length > 0 || unused.length > 0) process.exitCode = 1
