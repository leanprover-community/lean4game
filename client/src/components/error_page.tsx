import * as React from 'react'
import { useRouteError } from "react-router-dom";
import '../css/error_page.css'

export default function ErrorPage() {
  const error: any = useRouteError()
  console.error(error)

  return (
    <div id="error-page">
      <div className="error-message">
        <h1>Oops!</h1>
        <p>Something unexpected happened:</p>
        <p><code>({error.status}) {error.statusText || error.message}<br/>{error.data}</code></p>
        <p>Please create an issue at the <a href="https://github.com/leanprover-community/lean4game/issues" target="_blank">lean4game repo</a>.</p>
        <div className="thought-bubble" />
        <div className="thought-bubble" />
        <div className="thought-bubble" />
        <div className="thought-bubble" />
      </div>
    </div>
  )
}
