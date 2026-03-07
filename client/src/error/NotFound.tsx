import * as React from 'react'
import '../css/error_page.css'
import { useAtom } from 'jotai'

/** The 404 page */
export function NotFound() {
  return (
    <div id="error-page">
      <div className="error-message">
        <h1>This page could not be found</h1>
        <p><code>(404)</code> page {window.location.href} seems not to exist.</p>
        <p>If you believe it should, please create an issue at the <a href="https://github.com/leanprover-community/lean4game/issues" target="_blank">lean4game repo</a>.</p>
        <div className="thought-bubble" />
        <div className="thought-bubble" />
        <div className="thought-bubble" />
        <div className="thought-bubble" />
      </div>
    </div>
  )
}
