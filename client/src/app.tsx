import * as React from 'react';
import { useEffect, useRef } from 'react';
import { useAtom } from 'jotai';

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import './css/reset.css';
import './css/app.css';
import i18n from './i18n';
import { Popup } from './components/popup/popup';
import { leanMonacoAtom, leanMonacoOptionsAtom } from './store/editor-atoms';
import { LeanMonaco } from 'lean4monaco';
import { preferencesAtom } from './store/preferences-atoms';

function App({ children }: { children?: React.ReactNode }) {

  const infoviewRef = useRef<HTMLDivElement>(null)
  const [leanMonaco, setLeanMonaco] = useAtom(leanMonacoAtom)
  const [leanMonacoOptions] = useAtom(leanMonacoOptionsAtom)
  const [preferences] = useAtom(preferencesAtom)

  useEffect(() => {
    i18n.changeLanguage(preferences.language)
  }, [preferences.language])

  // You need to start one `LeanMonaco` instance once in your application using a `useEffect`
  useEffect(() => {
    const _leanMonaco = new LeanMonaco()
    setLeanMonaco(_leanMonaco)
    _leanMonaco.setInfoviewElement(infoviewRef.current!)

    ;(async () => {
      await _leanMonaco.start(leanMonacoOptions)
      console.debug('[lean4game]: leanMonaco started')
    })()

    return () => {
      if (leanMonaco && typeof leanMonaco?.dispose === "function") {
        leanMonaco?.dispose?.()
      }
    }
  }, [leanMonacoOptions, setLeanMonaco])

  return (
    <div className="app">
      <React.Suspense>
        {children}
      </React.Suspense>
      <Popup />
    </div>
  )
}

export default App
