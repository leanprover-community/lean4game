import * as React from 'react';
import { useNavigate, Link } from "react-router-dom";
import { Trans, useTranslation } from 'react-i18next';

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import '../../css/landing_page.css'
import bgImage from '../../assets/bg.jpg'

import { Markdown } from '../markdown';
import { GameTile, useGetGameInfoQuery } from '../../state/api'
import path from 'path';

import { ImpressumButton, MenuButton, PreferencesButton, PrivacyButton } from '../app_bar';
import ReactCountryFlag from 'react-country-flag';
import lean4gameConfig from '../../config.json'
import i18next from 'i18next';
import { popupAtom, PopupType } from '../../store/popup-atoms';
import { useAtom } from 'jotai';
import { GithubIcon } from '../navigation/github_icon';

/** One tile for a game visible on the front page */
export function Tile({gameId, data}: {gameId: string, data: GameTile|undefined}) {
  let { t } = useTranslation()
  let navigate = useNavigate();
  const routeChange = () =>{
    navigate(gameId);
  }

  if (typeof data === 'undefined') {
    return <></>
  }

  return <div className="game" onClick={routeChange}>
    <div className="wrapper">
      <div className="title">{t(data.title, { ns: gameId })}</div>
      <div className="short-description">{t(data.short, { ns: gameId })}
      </div>
      { data.image ? <img className="image" src={path.join("data", gameId, data.image)} alt="" /> : <div className="image"/> }
      <div className="long description"><Markdown>{t(data.long, { ns: gameId })}</Markdown></div>
    </div>
    <table className="info">
      <tbody>
      <tr>
        <td title="consider playing these games first.">{t("Prerequisites")}</td>
        <td><Markdown>{t(data.prerequisites.join(', '), { ns: gameId })}</Markdown></td>
      </tr>
      <tr>
        <td>{t("Worlds")}</td>
        <td>{data.worlds}</td>
      </tr>
      <tr>
        <td>{t("Levels")}</td>
        <td>{data.levels}</td>
      </tr>
      <tr className="languages">
        <td>{t("Language")}</td>

        <td>
          {data.languages.map((lang) => {
            let langOpt = lean4gameConfig.languages.find((e: { iso: string; }) => e.iso == lang)
            if (lean4gameConfig.useFlags) {
              return <ReactCountryFlag key={`flag-${lang}`} title={langOpt?.name} countryCode={langOpt?.flag} className="emojiFlag"/>
            } else {
              return <span title={langOpt?.name}>{lang}</span>
            }
          })}
        </td>
      </tr>
      </tbody>
    </table>
  </div>

}
