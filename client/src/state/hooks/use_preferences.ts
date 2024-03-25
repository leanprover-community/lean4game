import React, { useState } from "react";
import { useAppDispatch, useAppSelector } from "../../hooks";
import {
    PreferencesState,
    setLayout as setPreferencesLayout,
    setIsSavePreferences as setPreferencesIsSavePreferences,
    setLanguage as setLanguagePreferences,
    getWindowDimensions,
    AUTO_SWITCH_THRESHOLD
} from "../preferences";


const UsePreferences = () => {
    const dispatch = useAppDispatch()
    const [mobile, setMobile] = React.useState<boolean>()

    const layout = useAppSelector((state) => state.preferences.layout);
    const setLayout = (layout: PreferencesState["layout"]) => dispatch(setPreferencesLayout(layout))

    const isSavePreferences = useAppSelector((state) => state.preferences.isSavePreferences);
    const setIsSavePreferences = (isSave: boolean) => dispatch(setPreferencesIsSavePreferences(isSave))

    const language = useAppSelector((state) => state.preferences.language);
    const setLanguage = (lang: string) => dispatch(setLanguagePreferences(lang))

    const automaticallyAdjustLayout = () => {
        const {width} = getWindowDimensions()
        setMobile(width < AUTO_SWITCH_THRESHOLD)
    }

    React.useEffect(()=>{
        if (layout === "auto"){
          void automaticallyAdjustLayout()
          window.addEventListener('resize', automaticallyAdjustLayout)

          return () => window.removeEventListener('resize', automaticallyAdjustLayout)
        } else {
          setMobile(layout === "mobile")
        }
    }, [layout])

    return {mobile, layout, isSavePreferences, language, setLayout, setIsSavePreferences, setLanguage}
}

export default UsePreferences;
