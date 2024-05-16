import i18next from "i18next"
import React from "react"
import { useParams } from "react-router-dom"
import { GameIdContext } from "../app"
import { useGetGameInfoQuery } from "../state/api"

function Game() {
  const params = useParams()
  const levelId = parseInt(params.levelId)
  const worldId = params.worldId

  return <div>
    <GameIdContext.Provider value={gameId}></GameIdContext.Provider>

  </div>
}
