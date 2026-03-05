import * as React from 'react';
import { useEffect, useRef } from 'react';
import { Outlet } from "react-router-dom";
import { useAtom } from 'jotai';

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import './css/reset.css';
import './css/app.css';
import { PreferencesContext } from './components/infoview/context';
import UsePreferences from "./state/hooks/use_preferences"
import i18n from './i18n';
import { Popup } from './components/popup/popup';
import { leanMonacoAtom, leanMonacoOptionsAtom } from './store/editor-atoms';
import { LeanMonaco } from 'lean4monaco';
import { gameIdAtom } from './store/location-atoms';

function App({ children }: { children?: React.ReactNode }) {

  const {mobile, layout, isSavePreferences, language, isSuggestionsMobileMode, setLayout, setIsSavePreferences, setLanguage, setIsSuggestionsMobileMode} = UsePreferences()

  const infoviewRef = useRef<HTMLDivElement>(null)
  const [leanMonaco, setLeanMonaco] = useAtom(leanMonacoAtom)
  const [leanMonacoOptions] = useAtom(leanMonacoOptionsAtom)

  useEffect(() => {
    i18n.changeLanguage(language)
  }, [language])

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
      leanMonaco?.dispose?.()
    }
  }, [leanMonacoOptions, setLeanMonaco])

  return (
    <div className="app">
      <PreferencesContext.Provider value={{mobile, layout, isSavePreferences, language, isSuggestionsMobileMode, setLayout, setIsSavePreferences, setLanguage, setIsSuggestionsMobileMode}}>
        <React.Suspense>
          {children}
        </React.Suspense>
        <Popup />
      </PreferencesContext.Provider>
    </div>
  )
}

export default App
