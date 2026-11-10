import { useAtomValue } from 'jotai'

import { proofAtom } from '../../state/proof-atoms'
import { levelInfoAtom } from '../../state/query-atoms'

/**
 * A minimal alternative to the typewriter: the statement of the level and the player's
 * proof as plain Lean code, not editable.
 */
export function Raw() {
  const levelInfo = useAtomValue(levelInfoAtom).data
  const proof = useAtomValue(proofAtom)
  const statement = levelInfo?.descrFormat ?? ''
  const tactics = proof
    .flatMap(step => step.split('\n'))
    .map(line => '  ' + line)
  const code = [statement, ...tactics].join('\n')
  return (
    <div className="h-full overflow-auto p-2 text-left">
      <pre className="m-0 rounded-sm bg-(--code-bg) p-2 font-mono text-sm wrap-break-word whitespace-pre-wrap text-(--text-h)">
        <code className="block bg-transparent p-0">{code}</code>
      </pre>
    </div>
  )
}
