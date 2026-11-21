import { useSetAtom } from 'jotai'
import { twMerge } from 'tailwind-merge'

import { abbreviationsOf } from '../hooks/useAbbreviations'
import { insertAtom } from '../Masks/mask-atoms'

/**
 * The inventory's symbols tab: the Unicode symbols used in the game's sample proofs, see
 * `symbols` in `game.json`. Clicking one inserts it into the active mask like an item:
 * the typewriter puts it at the caret, like typing its abbreviation, the raw mask copies
 * it. The tooltip shows the abbreviations.
 */
export function SymbolList({ symbols }: { symbols: string[] }) {
  const insert = useSetAtom(insertAtom)
  return (
    <div className="grid min-h-0 flex-1 grid-cols-[repeat(auto-fill,2.25rem)] content-start justify-center gap-1 overflow-y-auto p-2">
      {symbols.map(symbol => {
        const abbreviations = abbreviationsOf(symbol)
        return (
          <button
            key={symbol}
            type="button"
            className={twMerge(
              'size-9 cursor-pointer rounded border border-(--border) font-mono text-lg',
              'text-(--text-h) hover:border-primary hover:text-primary',
            )}
            title={
              abbreviations.length > 0
                ? `${symbol}  ${abbreviations.join(', ')}`
                : symbol
            }
            // keeps the focus, and so the selection, in the typewriter's input
            onMouseDown={ev => ev.preventDefault()}
            onClick={() => insert({ kind: 'symbol', symbol })}
          >
            {symbol}
          </button>
        )
      })}
    </div>
  )
}
