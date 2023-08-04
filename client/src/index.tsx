import * as React from 'react';
import { createRoot } from 'react-dom/client';
import App from './app';
import { ConnectionContext, connection } from './connection'
import { store } from './state/store';
import { Provider } from 'react-redux';
import {
  createHashRouter,
  RouterProvider,
  Route,
} from "react-router-dom";
import ErrorPage from './components/error_page';
import Welcome from './components/welcome';
import LandingPage from './components/landing_page';
import Level from './components/level';
import { monacoSetup } from 'lean4web/client/src/monacoSetup';
import { redirect } from 'react-router-dom';

monacoSetup()

const router = createHashRouter([
  {
    path: "/",
    element: <LandingPage />,
  },
  {
    path: "/game/nng",
    loader: () => redirect("/g/hhu-adam/NNG4")
  },
  {
    path: "/g/:owner/:repo",
    element: <App />,
    errorElement: <ErrorPage />,
    children: [
      {
        path: "/g/:owner/:repo",
        element: <Welcome />,
      },
      {
        path: "/g/:owner/:repo/world/:worldId/level/:levelId",
        element: <Level />,
      },
    ],
  },
]);

const container = document.getElementById('root');
const root = createRoot(container!);
root.render(
  <React.StrictMode>
    <Provider store={store}>
      <ConnectionContext.Provider value={connection}>
        <RouterProvider router={router} />
      </ConnectionContext.Provider>
    </Provider>
  </React.StrictMode>
);
