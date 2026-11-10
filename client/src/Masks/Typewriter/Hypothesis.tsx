import { useSetAtom } from 'jotai'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import type { ApiHypothesis } from '../../api'
import { insertAtom } from '../mask-atoms'
import { HoverCode, LeanText } from './HoverCode'

export function HypGroup({
  title,
  hyps,
}: {
  title: string
  hyps: ApiHypothesis[]
}) {
  return (
    <div className="mb-1">
      <div className="font-sans text-lg">{title}:</div>
      {hyps.map((hyp, i) => (
        <div key={i}>
          <strong>
            {hyp.names.map(name => (
              <HypName key={name} name={name} />
            ))}
          </strong>
          &nbsp;:&nbsp;
          <HoverCode code={hyp.typeWithHover} fallback={hyp.type} />
          {/* never show the value of assumptions (proof irrelevance) */}
          {!hyp.isAssumption && hyp.value != null && (
            <>
              &nbsp;:=&nbsp;
              <HoverCode code={hyp.valueWithHover} fallback={hyp.value} />
            </>
          )}
        </div>
      ))}
    </div>
  )
}

/**
 * The name of a hypothesis. Clicking it inserts it in the active mask, except for
 * inaccessible names like `x✝`, which cannot be used.
 */
function HypName({ name }: { name: string }) {
  const { t } = useTranslation()
  const insert = useSetAtom(insertAtom)
  const className = 'm-0.5 inline-block h-6 min-w-6 rounded px-1 text-center'
  if (name.includes('✝'))
    return (
      <span
        className={twMerge(
          className,
          'bg-gray-100 text-gray-600 dark:bg-gray-800 dark:text-gray-400',
        )}
      >
        <LeanText text={name} />
      </span>
    )
  return (
    <button
      type="button"
      className={twMerge(
        className,
        'cursor-pointer border border-(--text) font-[inherit] text-amber-700',
        'hover:text-primary dark:text-amber-300',
      )}
      title={t('inventory.insert', { name })}
      onClick={() => insert({ kind: 'name', name })}
    >
      <LeanText text={name} />
    </button>
  )
}
