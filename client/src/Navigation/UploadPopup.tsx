import { useSetAtom } from 'jotai'
import { type ChangeEvent, type ReactNode, useId, useState } from 'react'
import { Trans, useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import { Button } from '../components/Button'
import { Popup } from '../components/Popup'
import { downloadProgressAtom, progressAtom } from '../state/progress-atoms'
import { parseGameProgress } from '../state/progress-schema'
import type { GameProgress } from '../state/progress-types'

/** Replaces the progress of the current game by the one in a JSON file */
export function UploadPopup({
  open,
  onClose,
}: {
  open: boolean
  onClose: () => void
}) {
  const { t } = useTranslation()
  const setProgress = useSetAtom(progressAtom)
  const downloadProgress = useSetAtom(downloadProgressAtom)
  const inputId = useId()
  // the validated file, or what is wrong with it
  const [upload, setUpload] = useState<
    { progress: GameProgress } | { error: string } | null
  >(null)

  const close = () => {
    setUpload(null)
    onClose()
  }

  const onFileChange = async (e: ChangeEvent<HTMLInputElement>) => {
    const file = e.target.files?.[0]
    setUpload(file ? parseGameProgress(await file.text()) : null)
  }

  const load = () => {
    if (!upload || !('progress' in upload)) return
    setProgress(upload.progress)
    close()
  }

  return (
    <Popup open={open} onClose={close} title={t('progress.uploadTitle')}>
      <div>
        <Trans
          i18nKey="progress.uploadDescription"
          components={{
            p: <p className="my-2" />,
            strong: <strong />,
            downloadLink: <DownloadLink onClick={downloadProgress} />,
          }}
        />
      </div>
      <p className="my-4">
        <label htmlFor={inputId} className="sr-only">
          {t('progress.selectFile')}
        </label>
        {/* remounted on opening, so that no file is selected */}
        <input
          key={String(open)}
          id={inputId}
          type="file"
          accept=".json,application/json"
          onChange={e => void onFileChange(e)}
          className={twMerge(
            'max-w-full',
            // the button to choose a file
            'file:mr-3 file:cursor-pointer file:rounded file:bg-primary file:px-3',
            'file:py-1.5 file:text-white hover:file:bg-primary/85',
          )}
        />
      </p>
      {upload && 'error' in upload && (
        <p role="alert" className="my-2 wrap-break-word text-error">
          {t('progress.invalidFile', { error: upload.error })}
        </p>
      )}
      <Button onClick={load} disabled={!upload || !('progress' in upload)}>
        {t('progress.load')}
      </Button>
    </Popup>
  )
}

/** The link to download the current progress, its text is passed by `<Trans>` */
function DownloadLink({
  onClick,
  children,
}: {
  onClick: () => void
  children?: ReactNode
}) {
  return (
    <button
      type="button"
      className="cursor-pointer text-primary underline"
      onClick={onClick}
    >
      {children}
    </button>
  )
}
