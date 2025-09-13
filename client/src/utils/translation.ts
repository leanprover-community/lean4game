import { useContext } from 'react'
import { useTranslation, UseTranslationResponse } from 'react-i18next'
import { GameIdContext } from '../app'

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
  key: string,
  codeBlocks: string[],
} {
  const regex = /((?<!\\)(`+|\${1,2})([\s\S]*?)\2)/g;
  const blocks: string[] = []
  let modified = input
  let index = 0
  // Collect code blocks and replace them with placeholders
  modified = modified.replace(regex, (match, _full, _ticks, _content) => {
    blocks.push(match)
    const placeholder = `§${index}`
    index++
    return placeholder
  });
  return { key: modified, codeBlocks: blocks }
}

/**
 * Wrapper around the hook obtained from `useTranslation`.
 * Add the game-ID namespace and replace code blocks according to
 * the translation keys received from `lean-i18n`.
 */
export function useGameTranslation(): UseTranslationResponse<'translation', undefined> {
  const gameId = useContext(GameIdContext)
  const { t, ...rest } = useTranslation()
  const pattern = /(?<!\\)§(\d+)/g;
  const modifiedT = ((key: string | undefined) => {
    if (!key) return ""
    const { codeBlocks, key: keyWithoutBlocks } = extractCodeBlocks(key)
    let translatedKey = t(keyWithoutBlocks, {ns: gameId})
    return translatedKey.replace(pattern, (_, num: string) => codeBlocks[Number(num)] ?? num);
  }) as typeof t
  return { t: modifiedT, ...rest }
}
