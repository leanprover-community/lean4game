import { StrictMode, Suspense } from 'react'
import { createRoot } from 'react-dom/client'

import './index.css'
import { App } from './App.tsx'
import { Spinner } from './components/Spinner.tsx'
import { ErrorBoundary } from './ErrorPage/ErrorBoundary.tsx'

createRoot(document.getElementById('root')!).render(
  <StrictMode>
    <ErrorBoundary>
      <Suspense fallback={<Spinner />}>
        <App />
      </Suspense>
    </ErrorBoundary>
  </StrictMode>,
)
