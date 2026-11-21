import { useAtomValue } from 'jotai'
import { useEffect, useState } from 'react'
import { useTranslation } from 'react-i18next'

import { leanPhaseAtom } from '../state/proof-atoms'

/** The text for what the Lean instance is doing, see `leanPhaseAtom` */
export function useLeanPhaseText() {
  const { t } = useTranslation()
  const phase = useAtomValue(leanPhaseAtom)
  const texts = {
    starting: t('masks.phase.starting'),
    loading: t('masks.phase.loading'),
    checking: t('masks.phase.checking'),
  }
  return texts[phase]
}

/** A hint shown below the text of the phase, see `useLeanPhaseText` */
function useLeanPhaseHint() {
  const { t } = useTranslation()
  const phase = useAtomValue(leanPhaseAtom)
  return phase === 'loading' ? t('masks.phase.loadingHint') : undefined
}

/**
 * What Lean is doing while the first result of a level is awaited, and for how long
 * already: loading the imports of a game, e.g. all of Mathlib, can take a while.
 */
export function LeanProgress() {
  const { t } = useTranslation()
  const text = useLeanPhaseText()
  const hint = useLeanPhaseHint()
  const [start] = useState(() => Date.now())
  const [now, setNow] = useState(start)
  useEffect(() => {
    const interval = setInterval(() => setNow(Date.now()), 1000)
    return () => clearInterval(interval)
  }, [])
  const seconds = Math.floor((now - start) / 1000)
  return (
    <output className="block max-w-sm text-center text-sm text-balance text-(--text)">
      <span className="block">{text}</span>
      {hint && <span className="block">{hint}</span>}
      {seconds >= 3 && (
        <span className="block">{t('masks.elapsed', { seconds })}</span>
      )}
    </output>
  )
}
