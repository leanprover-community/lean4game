import * as React from 'react';
import { createRoot } from 'react-dom/client';
import './index.css';
import App from './App';
import Level from './components/Level';
import { ConnectionContext, connection } from './connection'
import { store } from './store';
import { Provider } from 'react-redux';
import {
  createHashRouter,
  RouterProvider,
  Route,
} from "react-router-dom";
import "./index.css";
import { monacoSetup } from 'lean4web/client/src/monacoSetup';

monacoSetup()

const router = createHashRouter([
  {
    path: "/",
    element: <App />,
    children: [
      {
        path: "/",
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
