import * as React from 'react';
import { Typography } from '@mui/material'
import { Markdown } from '../utils'
import { Trans, useTranslation } from 'react-i18next'
import { useSelector } from 'react-redux'
import { selectLevel } from '../../state/progress'
import { useGetGameInfoQuery } from '../../state/api'
import { GameIdContext, ProofContext } from '../../state/context'

/** Pop-up that is displaying when opening the 'Report Problem' button.
 *
 * 
 * 
 */
export function ReportProblemPopup () {
	const { t } = useTranslation()
	const { gameId } = React.useContext(GameIdContext)
	const gameIdShort = gameId.replace("g/local/", "") // If local, remove the first part of the string
	const gameInfo = useGetGameInfoQuery({game: gameId})
	const level = useSelector(selectLevel(gameId))
	
	const { proofState } = React.useContext(ProofContext)
	console.log("level")
	console.log(level)
	console.log("proofState")
	console.log(proofState)
    const issueTitle = `Issue with level ${level}`
    const issueBody = `Describe the issue with level ${level} here: \n\n${proofState}`
	
	const repoUrl = `https://github.com/leanprover-community/${gameIdShort}`
	const url = new URL(`${repoUrl}/issues/new`)
	url.searchParams.set('title', issueTitle)
	url.searchParams.set('body', issueBody)
	
    return (
        <button
          onClick={() => open(url)}
          style={{ padding: '10px 20px', fontSize: '16px', cursor: 'pointer' }}
        >
          Report an Issue
        </button>
      );
}
