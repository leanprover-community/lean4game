import * as React from 'react';
import { useState, useEffect } from 'react';
import { Outlet } from "react-router-dom";

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import './reset.css';
import './app.css';

function App() {
  return (
    <div className="app">
      <Outlet />
    </div>
  )
}

export default App
