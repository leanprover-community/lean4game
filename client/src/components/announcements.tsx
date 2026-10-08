import * as React from 'react'
import { useTranslation } from 'react-i18next'
import { Markdown } from './markdown'

interface Announcement {
  id: string
  title: Record<string, string>
  message: Record<string, string>
  endsAt?: string
}

function localized(text: Record<string, string>, languages: string[]): string {
  for (const language of languages) {
    if (text[language]) return text[language]
    const baseLanguage = language.split('-')[0]
    if (text[baseLanguage]) return text[baseLanguage]
  }
  return text.en
}

export function Announcements() {
  const { i18n } = useTranslation()
  const [announcements, setAnnouncements] = React.useState<Announcement[]>([])
  const languages = [i18n.language, ...(i18n.languages ?? [])]

  React.useEffect(() => {
    let mounted = true
    let controller: AbortController | undefined

    async function refresh() {
      // Avoid overlapping responses overwriting a newer notice list.
      controller?.abort()
      controller = new AbortController()
      try {
        const response = await fetch('/data/announcements', {
          cache: 'no-store',
          signal: controller.signal,
        })
        if (!response.ok) throw new Error(`Announcements returned HTTP ${response.status}`)
        const data = await response.json()
        if (!Array.isArray(data.announcements)) throw new Error('Invalid announcements response')
        if (mounted) setAnnouncements(data.announcements)
      } catch (error) {
        if (error instanceof Error && error.name === 'AbortError') return
        // Keep the last notices during a temporary outage, but remove expired ones.
        if (mounted) {
          setAnnouncements(current => current.filter(entry => !entry.endsAt || Date.now() < Date.parse(entry.endsAt)))
          console.info('Announcements unavailable', error)
        }
      }
    }

    void refresh()
    const interval = window.setInterval(() => { void refresh() }, 60_000)
    return () => {
      mounted = false
      controller?.abort()
      window.clearInterval(interval)
    }
  }, [])

  if (announcements.length === 0) return null

  return <section className="announcements" aria-live="polite">
    <div className="wrapper">
      {announcements.map(entry => <article className="announcement" key={entry.id}>
        <h2>{localized(entry.title, languages)}</h2>
        <Markdown>{localized(entry.message, languages)}</Markdown>
      </article>)}
    </div>
  </section>
}
