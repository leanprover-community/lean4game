import * as React from 'react'
import { MenuItem, Select, SelectChangeEvent, Typography } from '@mui/material'
import { Switch } from '@mui/material';
import Box from '@mui/material/Box';
import Slider from '@mui/material/Slider';
import lean4gameConfig from '../../config.json'

import FormControlLabel from '@mui/material/FormControlLabel';

import ReactCountryFlag from 'react-country-flag';
import { useTranslation } from 'react-i18next';
import { useAtom } from 'jotai';
import { preferencesAtom } from '../../store/preferences-atoms';

export function PreferencesPopup() {
  let { t } = useTranslation()
  const [preferences, setPreferences] = useAtom(preferencesAtom)

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

  const handlerChangeLayout = (_: Event, val: number | number[]) => {
    const newLayout = val == 0 ? "mobile": val == 1 ? "auto" : "desktop"
    setPreferences(prev => ({ ...prev, layout: newLayout }))
  }

  const handlerChangeLanguage = (ev: SelectChangeEvent<string>) => {
    setPreferences(prev => ({ ...prev, language: ev.target.value }))
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
                    value={preferences.language}
                    label={t("Language")}
                    onChange={handlerChangeLanguage}>
                      {lean4gameConfig.languages.map(lang => {
                        return <MenuItem key={`menu-item-lang-${lang.iso}`} value={lang.iso}>
                          {preferences.useFlags && <ReactCountryFlag countryCode={lang.flag}/>}
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
          <div className='preferences-item'>
            <FormControlLabel
              control={
                <Switch
                  checked={preferences.useFlags}
                  onChange={() => setPreferences(prev => ({ ...prev, useFlags: !preferences.useFlags }))}
                  name="checked"
                  color="primary"
                />
              }
              label={t("Use country flags to represent languages")}
              labelPlacement="end"
            />
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
                    value={marks.find(item => item.key === preferences.layout)?.value}
                    step={1}
                    marks={marks}
                    max={2}
                    sx={{
                      '& .MuiSlider-track': { display: 'none', },
                    }}
                    onChange={(ev, val) => handlerChangeLayout(ev, val)}
                  />
                </Box>
              }
              label=""
            />
          </div>
          <div className='preferences-item'>
            <FormControlLabel
              control={
                <Switch
                  checked={preferences.showLockedInventory}
                  onChange={() => setPreferences(prev => ({ ...prev, hideLockedInventory: !preferences.showLockedInventory }))}
                  name="checked"
                  color="primary"
                />
              }
              label={t("Show locked inventory items")}
              labelPlacement="end"
            />
          </div>
        </div>
        <div className='preferences-category'>
          <div className='category-title'>
            <h3>{t("Controls")}</h3>
          </div>
          <p>---</p>
        </div>
        <div className='preferences-category tail-category'>
          <div className='category-title'>
            <h3>{t("Browser Storage")}</h3>
          </div>
          <div className='preferences-item'>
            <FormControlLabel
              control={
                <Switch
                  checked={preferences.isSavePreferences}
                  onChange={() => setPreferences(prev => ({ ...prev, isSavePreferences: !preferences.isSavePreferences }))}
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
