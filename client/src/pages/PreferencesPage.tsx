import { useAtom, useAtomValue } from 'jotai'
import type { ReactNode } from 'react'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import { Switch } from '../components/Switch'
import config from '../config.json'
import { setLanguage } from '../i18n'
import {
  type Preferences,
  preferencesAtom,
  themeAtom,
} from '../state/preferences-atoms'

const themes = [
  'light',
  'auto',
  'dark',
] as const satisfies Preferences['theme'][]

const layouts = [
  'mobile',
  'auto',
  'desktop',
] as const satisfies Preferences['layout'][]

/** The settings of the user, see `preferencesAtom` */
export function PreferencesPage() {
  const { t, i18n } = useTranslation()
  const [preferences, setPreferences] = useAtom(preferencesAtom)
  const theme = useAtomValue(themeAtom)
  const update = (changes: Partial<Preferences>) =>
    setPreferences(prev => ({ ...prev, ...changes }))

  return (
    <div className="mx-auto flex-col w-full max-w-3xl gap-8 p-8 text-left">
      <h2>{t('preferences.title')}</h2>

      <Category title={t('preferences.language')}>
        <select
          className={twMerge(
            'w-72 rounded border border-(--border) bg-(--bg) px-3 py-2',
            'text-(--text-h)',
          )}
          aria-label={t('preferences.language')}
          value={i18n.language}
          onChange={ev => setLanguage(ev.target.value)}
        >
          {config.languages.map(({ iso, name }) => (
            <option key={iso} value={iso}>
              {name}
            </option>
          ))}
        </select>
        <p>{t('preferences.languageNote')}</p>
        <Switch
          checked={preferences.useFlags}
          onChange={useFlags => update({ useFlags })}
          label={t('preferences.useFlags')}
        />
      </Category>

      <Category title={t('preferences.layout')}>
        <Choice
          name="layout"
          label={t('preferences.layout')}
          options={layouts.map(layout => ({
            value: layout,
            label: t(`preferences.layouts.${layout}`),
          }))}
          value={preferences.layout}
          onChange={layout => update({ layout })}
        />
        <Switch
          checked={preferences.showLockedInventory}
          onChange={showLockedInventory => update({ showLockedInventory })}
          label={t('preferences.showLockedInventory')}
        />
      </Category>

      <Category title={t('preferences.theme')}>
        <Choice
          name="theme"
          label={t('preferences.theme')}
          options={themes.map(option => ({
            value: option,
            label: t(`preferences.themes.${option}`),
          }))}
          value={theme}
          onChange={value => update({ theme: value })}
        />
      </Category>

      <Category title={t('preferences.browserStorage')}>
        <Switch
          checked={preferences.isSavePreferences}
          onChange={isSavePreferences => update({ isSavePreferences })}
          label={t('preferences.savePreferences')}
        />
      </Category>
    </div>
  )
}

function Category({ title, children }: { title: string; children: ReactNode }) {
  return (
    <section className="flex-col gap-3">
      <h3 className="text-lg font-medium text-(--text-h)">{title}</h3>
      {children}
    </section>
  )
}

/** Buttons to choose exactly one of the `options` */
function Choice<T extends string>({
  name,
  label,
  options,
  value,
  onChange,
}: {
  name: string
  label: string
  options: { value: T; label: string }[]
  value: T
  onChange: (value: T) => void
}) {
  return (
    <div
      role="radiogroup"
      aria-label={label}
      className="inline-flex self-start overflow-hidden rounded border border-primary"
    >
      {options.map(option => (
        <label
          key={option.value}
          className={twMerge(
            'cursor-pointer px-4 py-2 has-checked:bg-primary has-checked:text-white',
            'has-focus-visible:outline-2 has-focus-visible:-outline-offset-4',
            'has-focus-visible:outline-white',
          )}
        >
          <input
            type="radio"
            name={name}
            className="sr-only"
            checked={value === option.value}
            onChange={() => onChange(option.value)}
          />
          {option.label}
        </label>
      ))}
    </div>
  )
}
