import { faSpinner } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { useAtomValue, useSetAtom } from 'jotai'
import { type SubmitEvent, useEffect, useRef, useState } from 'react'
import { Trans, useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import { Button } from '../components/Button'
import { Category } from '../pages/PreferencesPage'
import { HttpError } from '../utils/fetch'
import {
  currentImportAtom,
  importStatusAtom,
  startImportAtom,
} from './import-atoms'

/** Imports a game from GitHub and shows the messages of the server while doing so */
export function ImportPage() {
  const { t } = useTranslation()
  const current = useAtomValue(currentImportAtom)
  const startImport = useSetAtom(startImportAtom)
  const { data: status, error: statusError } = useAtomValue(importStatusAtom)
  const [owner, setOwner] = useState(current?.owner ?? '')
  const [repo, setRepo] = useState(current?.repo ?? '')
  const [starting, setStarting] = useState(false)
  const [startError, setStartError] = useState<Error | null>(null)

  const onSubmit = async (ev: SubmitEvent<HTMLFormElement>) => {
    ev.preventDefault()
    setStartError(null)
    setStarting(true)
    try {
      await startImport(owner.trim(), repo.trim())
    } catch (error) {
      setStartError(error as Error)
    }
    setStarting(false)
  }

  const startErrorMessage = (error: Error) => {
    if (error instanceof HttpError && error.status === 400) {
      return t('import.invalidName')
    }
    if (error instanceof HttpError && error.status === 429) {
      return t('import.rateLimited', { seconds: error.retryAfterSeconds })
    }
    return t('import.startError', { error: error.message })
  }

  const running = status?.state === 'running' && !statusError
  // the status of a new import has not arrived yet
  const waitingForStatus = current !== null && !status && !statusError
  const busy = starting || running || waitingForStatus
  const canStart = owner.trim().length > 0 && repo.trim().length > 0 && !busy

  return (
    <div className="mx-auto flex-col w-full max-w-3xl gap-8 p-8 text-left">
      <h2>{t('import.title')}</h2>
      <p>
        <Trans
          i18nKey="import.description"
          components={{
            skeletonLink: (
              <a
                href="https://github.com/hhu-adam/GameSkeleton"
                target="_blank"
                rel="noreferrer"
                aria-label="open GameSkeleton repo"
              />
            ),
          }}
        />
      </p>

      <form className="flex-col gap-3" onSubmit={ev => void onSubmit(ev)}>
        <NameInput
          label={t('import.owner')}
          value={owner}
          disabled={busy}
          onChange={setOwner}
        />
        <NameInput
          label={t('import.repo')}
          value={repo}
          disabled={busy}
          onChange={setRepo}
        />
        <Button type="submit" className="self-start" disabled={!canStart}>
          {t('import.start')}
        </Button>
      </form>

      {startError && (
        <p role="alert" className="wrap-break-word text-error">
          {startErrorMessage(startError)}
        </p>
      )}

      {current && (
        <Category title={t('import.messages')}>
          {status && (
            <>
              <output>
                {t(`import.states.${status.state}`)}
                {running && (
                  <FontAwesomeIcon
                    icon={faSpinner}
                    spinPulse
                    className="ml-2"
                  />
                )}
              </output>
              {status.warnings.map(warning => (
                <p
                  key={warning}
                  className={twMerge(
                    'rounded-sm bg-amber-100 px-2.5 py-1.5 text-amber-800',
                    'dark:bg-amber-950 dark:text-amber-200',
                  )}
                >
                  {warning}
                </p>
              ))}
              <ImportLog lines={status.log} />
            </>
          )}
          {statusError && (
            <p role="alert" className="wrap-break-word text-error">
              {t('import.statusError', { error: statusError.message })}
            </p>
          )}
        </Category>
      )}
    </div>
  )
}

function NameInput({
  label,
  value,
  disabled,
  onChange,
}: {
  label: string
  value: string
  disabled: boolean
  onChange: (value: string) => void
}) {
  return (
    <label className="flex-col flex gap-1">
      {label}
      <input
        type="text"
        autoCapitalize="none"
        autoCorrect="off"
        spellCheck={false}
        className={twMerge(
          'w-72 max-w-full rounded border border-(--border) bg-(--bg) px-3 py-2',
          'text-(--text-h) disabled:cursor-default disabled:opacity-50',
        )}
        value={value}
        disabled={disabled}
        onChange={ev => onChange(ev.target.value)}
      />
    </label>
  )
}

/** The lines of the server, scrolled to the newest one */
function ImportLog({ lines }: { lines: string[] }) {
  const ref = useRef<HTMLPreElement>(null)

  useEffect(() => {
    if (ref.current && lines.length > 0) {
      ref.current.scrollTop = ref.current.scrollHeight
    }
  }, [lines.length])

  return (
    <pre
      ref={ref}
      role="log"
      className={twMerge(
        'max-h-96 min-h-16 overflow-y-auto rounded-sm bg-(--section-bg) p-2.5',
        'font-mono text-sm wrap-break-word whitespace-pre-wrap',
      )}
    >
      {lines.join('\n')}
    </pre>
  )
}
