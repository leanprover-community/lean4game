/**
 * @fileOverview The impressum/privacy policy
*/
import { faShield } from '@fortawesome/free-solid-svg-icons';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';
import * as React from 'react'

/** Pop-up that is displayed when opening the privacy policy.
 *
 * `handleClose` is the function to close it again because it's open/closed state is
 * controlled by the containing element.
 *
 * Note: Do not translate the Impressum!
 */
export function PrivacyPolicyPopup ({handleClose}: {handleClose: () => void}) {
  return <div className="privacy-policy modal-wrapper">
  <div className="modal-backdrop" onClick={handleClose} />
  <div className="modal">
    <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
    <h2>Privacy Policy &amp; Impressum</h2>
    <p>
      Our server collects metadata (such as IP address, browser, operating system)
      and the data that the user enters into the editor. The data is used to
      compute the Lean output and display it to the user. The information will be stored
      as long as the user stays on our website and will be deleted immediately afterwards.
      We keep logs to improve our software, but the contained data is anonymized.
    </p>
    <p>
      We do not use cookies, but your game progress is stored in the browser
      as site data. Your game progress is not saved on the server; if you delete
      your browser storage, it is completely gone.
    </p>
    <p>Our server is located in Germany.</p>
    <p>
      <strong>Contact information:</strong><br />
        <strong>Impressum:</strong><br />
        Marcus Zibrowius<br />
        Mathematisches Institut der Heinrich-Heine-Universität Düsseldorf<br />
        Universitätsstr. 1<br />
        40225 Düsseldorf<br />
        Germany<br />
        +49 211 81 13858<br />
        <a href="https://www.math.uni-duesseldorf.de/~zibrowius/">Contact Details</a><br />
        <a href="mailto:matvey.lorkish@hhu.de?subject=Lean4Game: <Your%20Question>">Technical Contact</a>
    </p>
    <h2>Development &amp; Funding</h2>
    <p>
      The source code of this Lean game engine
      is <a href="https://github.com/leanprover-community/lean4game" target="_blank">available on Github</a>.
      If you experience any problems, please
      file an <a href="https://github.com/leanprover-community/lean4game/issues" target="_blank">Issue on Github</a> or
      get directly in contact.
    </p>
    <p>
      The game engine has been developed as part of the
      project <a href="https://hhu-adam.github.io/" target="_blank">ADAM: Anticipating the Digital
      Age of Mathematics</a> at
      Heinrich-Heine-Universität Düsseldorf. It is funded by
      the <i>Stiftung Innovation in der Hochschullehre</i> as part of project <i>Freiraum 2022</i>.
    </p>
  </div>
</div>
}
