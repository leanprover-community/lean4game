import * as React from 'react'
import '../css/error_page.css'

/** The fallback error page */
export function ErrorPage({ error }: { error: Error }) {

  return (
    <div id="error-page">
      <div className="error-message">
        <h1>Oops!</h1>
        <p>Something unexpected happened:</p>
        <p><code>({error.name}) {error.message}</code></p>
        <p>Please create an issue at the <a href="https://github.com/leanprover-community/lean4game/issues" target="_blank">lean4game repo</a>.</p>
        <div className="thought-bubble" />
        <div className="thought-bubble" />
        <div className="thought-bubble" />
        <div className="thought-bubble" />
      </div>
    </div>
  )
}
