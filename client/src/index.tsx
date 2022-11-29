import * as React from 'react';
import { createRoot } from 'react-dom/client';
import './index.css';
import App from './App';
import { store } from './store';
import { Provider } from 'react-redux';
import { ConnectionContext, leanClient } from './connection'


const container = document.getElementById('root');
const root = createRoot(container!);
root.render(
  <React.StrictMode>
    <Provider store={store}>
      <ConnectionContext.Provider value={leanClient}>
        <App />
      </ConnectionContext.Provider>
    </Provider>
  </React.StrictMode>
);
