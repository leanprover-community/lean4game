import * as React from 'react'
import { Input, MenuItem, Select, SelectChangeEvent, Typography } from '@mui/material'
import { Markdown } from '../markdown'
import { Switch, Button, ButtonGroup } from '@mui/material';
import Box from '@mui/material/Box';
import Slider from '@mui/material/Slider';
import lean4gameConfig from '../../config.json'

import FormControlLabel from '@mui/material/FormControlLabel';

import { IPreferencesContext, PreferencesContext } from "../infoview/context"
import ReactCountryFlag from 'react-country-flag';
import { useTranslation } from 'react-i18next';

export function PreferencesPopup() {
  let { t } = useTranslation()
  const {layout, isSavePreferences, language, isSuggestionsMobileMode, setLayout, setIsSavePreferences, setLanguage, setIsSuggestionsMobileMode} = React.useContext(PreferencesContext)

  const marks = [
    {
      value: 0,
      label: t('Mobile'),
      key: "mobile"
    },
    {
      value: 1,
      label: t('Auto'),
      key: "auto"
    },
    {
      value: 2,
      label: t('Desktop'),
      key: "desktop"
    },
  ];

  const handlerChangeLayout = (_: Event, value: number) => {
    setLayout(marks[value].key as IPreferencesContext["layout"])
  }

  const handlerChangeLanguage = (ev: SelectChangeEvent<string>) => {
    setLanguage(ev.target.value as IPreferencesContext["language"])
  }

  return <Typography variant="body1" component="div" className="settings">
        <div className='preferences-category'>
          <div className='category-title'>
            <h3>{t("Language")}</h3>
          </div>
          <div className='preferences-item first leave-left-gap'>
            <FormControlLabel
              control={
                <Box sx={{ width: 300 }}>
                  <Select
                    value={language}
                    label={t("Language")}
                    onChange={handlerChangeLanguage}>
                      {lean4gameConfig.languages.map(lang => {
                        return <MenuItem key={`menu-item-lang-${lang.iso}`} value={lang.iso}>
                          {lean4gameConfig.useFlags && <ReactCountryFlag countryCode={lang.flag}/>}
                          &nbsp;
                          {lang.name}
                        </MenuItem>
                      })}
                  </Select>
                </Box>
              }
              label=""
            />
            <p>
              If a game does not exist in the language selected, this setting has no effect
              and the game's default language is used.
            </p>
          </div>
        </div>
        <div className='preferences-category'>
          <div className='category-title'>
            <h3>{t("Layout")}</h3>
          </div>
          <div className='preferences-item first leave-left-gap'>
            <FormControlLabel
              control={
                <Box sx={{ width: 300 }}>
                  <Slider
                    aria-label={t("Always visible")}
                    value={marks.find(item => item.key === layout).value}
                    step={1}
                    marks={marks}
                    max={2}
                    sx={{
                      '& .MuiSlider-track': { display: 'none', },
                    }}
                    onChange={handlerChangeLayout}
                  />
                </Box>
              }
              label=""
            />
          </div>
        </div>
        <div className='preferences-category'>
          <div className='category-title'>
            <h3>{t("Controls")}</h3>
          </div>
          <div className='preferences-item'>
            <FormControlLabel
              control={
                <Switch
                  checked={isSuggestionsMobileMode}
                  onChange={() => setIsSuggestionsMobileMode(!isSuggestionsMobileMode)}
                  name="checked"
                  color="primary"
                />
              }
              label={t("Click on tactics/assumptions like mobile keyboard suggestions i.e. without autofocus or requiring Shift key")}
              labelPlacement="end"
            />
          </div>
        </div>
        <div className='preferences-category tail-category'>
          <div className='preferences-item'>
            <FormControlLabel
              control={
                <Switch
                  checked={isSavePreferences}
                  onChange={() => setIsSavePreferences(!isSavePreferences)}
                  name="checked"
                  color="primary"
                />
              }
              label={t("Save my settings (in the browser store)")}
              labelPlacement="end"
            />
          </div>
        </div>
      </Typography>
}
