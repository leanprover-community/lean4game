import * as React from 'react';
import { useNavigate } from "react-router-dom";
import { useTranslation } from 'react-i18next';
import { Markdown } from '../markdown';
import { GameTile } from '../../state/api'
import { Flag } from '../flag';
import path from 'path';

/** One tile for a game visible on the front page */
export function Tile({gameId, data}: {gameId: string, data: GameTile | undefined}) {
  let { t } = useTranslation()
  let navigate = useNavigate()

  if (!data) return null

  return <div className="game" onClick={() => navigate(gameId)}>
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
          {data.languages.map((lang) => (
            <Flag key={lang} iso={lang} showTitle={true} />
          ))}
        </td>
      </tr>
      </tbody>
    </table>
  </div>
}
