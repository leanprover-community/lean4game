import { useEffect, useState } from 'react'
import { useTranslation } from 'react-i18next'

import { getGameI18n } from '../i18n'

/**
 * This file provides the tools to process translations created by the Lean package `lean-i18n`.
 *
 * The Lean package `lean-i18n` filters code blocks and latex blocks from the texts before
 * storing them for translation. These are replaced by placeholders of the form `§n`.
 *
 * However, in the game data (json files) the original strings including
 * these blocks are contained.
 * Thus, we mirror the block replacement `lean-i18n` does before trying to translate
 * the texts which have the blocks replaced.
 */

/**
 * Extract code blocks and latex blocks, search for translations and plug the translations
 * into the translated string.
 *
 * Note: This function must be functionally equivalent to the corresponding function
 * from the `lean-i18n` package!
 */
function extractCodeBlocks(input: string): {
  key: string
  codeBlocks: string[]
} {
  const regex = /((?<!\\)(`+|\${1,2})([\s\S]*?)\2)/g
  const blocks: string[] = []
  let index = 0
  // Collect code blocks and replace them with placeholders
  const modified = input.replace(regex, match => {
    blocks.push(match)
    const placeholder = `§${index}`
    index++
    return placeholder
  })
  return { key: modified, codeBlocks: blocks }
}

/**
 * Translates texts of the game `gameId`, e.g. `g/owner/repo`, into the current language.
 * Replaces code blocks according to the translation keys received from `lean-i18n`.
 *
 * With `allowEmptyTranslations` (from the game's settings), an empty translation hides
 * the text, otherwise it counts as missing and the original text is shown.
 */
export function useGameTranslation(
  gameId: string,
  allowEmptyTranslations = false,
) {
  const { i18n } = useTranslation()
  const lng = i18n.resolvedLanguage ?? i18n.language

  // the namespace of the game is loaded from the server, re-render once it is there.
  // On a language change, i18next loads it in the new language by itself.
  const [, setLoaded] = useState(0)
  useEffect(() => {
    let active = true
    void i18n.loadNamespaces(gameId).then(() => {
      if (active) setLoaded(n => n + 1)
    })
    return () => {
      active = false
    }
  }, [i18n, gameId])

  // the keys are whole texts, so `.` must not separate nested keys
  const gameT = getGameI18n(allowEmptyTranslations).getFixedT(lng) as (
    keys: string[],
    options: { ns: string; keySeparator: false },
  ) => string
  const pattern = /(?<!\\)§(\d+)/g

  const t = (key: string | undefined): string => {
    if (!key) return ''
    const { codeBlocks, key: keyWithoutBlocks } = extractCodeBlocks(key)
    // lean-i18n doubles backslashes outside code blocks in catalog keys.
    const escapedKey = keyWithoutBlocks.replace(/\\/g, '\\\\')
    // Keep the older placeholder and raw keys as fallbacks for existing catalogs.
    const translatedKey = gameT([escapedKey, keyWithoutBlocks, key], {
      ns: gameId,
      keySeparator: false,
    })
    return translatedKey.replace(
      pattern,
      (_, num: string) => codeBlocks[Number(num)] ?? num,
    )
  }
  return { t, i18n }
}
