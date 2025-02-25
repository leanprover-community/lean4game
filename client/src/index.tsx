import * as React from 'react'
import { createRoot } from 'react-dom/client'
import App from './app'
import { store } from './state/store'
import { Provider } from 'react-redux'
import type { RouteObject } from "react-router"
import { createHashRouter, RouterProvider, Route, redirect } from "react-router-dom"
import ErrorPage from './components/error_page'
import LandingPage from './components/landing_page'
import './i18n'
import Game from './components/game'



// If `VITE_LEAN4GAME_SINGLE` is set to true, then `/` should be redirected to
// `/g/local/game`. This is used for the devcontainer setup
let single_game = (import.meta.env.VITE_LEAN4GAME_SINGLE == "true")
// let root_object: RouteObject = single_game ? {
//   path: "/",
//   loader: () => redirect("/g/local/game")
// }

let landing_page: RouteObject = single_game ? {
    path: "/",
    loader: () => redirect("/g/local/game")
  } : {
    path: "/",
    element: <LandingPage />,
  }

const router = createHashRouter([
  // root_object,
  {
    // For backwards compatibility
    path: "/game/nng",
    loader: () => redirect("/g/leanprover-community/nng4")
  },
  {
    // For backwards compatibility
    path: "/g/hhu-adam/NNG4",
    loader: () => redirect("/g/leanprover-community/nng4")
  },
  {
    path: "/",
    element: <App />,
    errorElement: <ErrorPage />,
    children: [
      landing_page,
      {
        path: "/g/:owner/:repo",
        element: <Game />,
      },
      {
        path: "/g/:owner/:repo/world/:worldId/level/:levelId",
        element: <Game />,
      },
    ],
  },
])

const container = document.getElementById('root')
const root = createRoot(container!)
root.render(
  <React.StrictMode>
    <Provider store={store}>
      <RouterProvider router={router} />
    </Provider>
  </React.StrictMode>
)
