import { Trans, useTranslation } from 'react-i18next'

import { ErrorMessage, IssueLink } from './ErrorMessage'

/** The fallback page for uncaught errors */
export function ErrorPage({ error }: { error?: Error }) {
  const { t } = useTranslation()
  return (
    <ErrorMessage>
      <h2>{t('errorPage.title')}</h2>
      <p>{t('errorPage.description')}</p>
      {error && (
        <p>
          <code className="w-full">
            ({error.name}) {error.message}
          </code>
        </p>
      )}
      <p>
        <Trans
          i18nKey="errorPage.createIssue"
          components={{ issueLink: <IssueLink /> }}
        />
      </p>
    </ErrorMessage>
  )
}
