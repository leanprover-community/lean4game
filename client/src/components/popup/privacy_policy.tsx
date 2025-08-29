/**
 * @fileOverview The impressum/privacy policy
*/
import { faShield } from '@fortawesome/free-solid-svg-icons';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';
import * as React from 'react'
import { Trans, useTranslation } from 'react-i18next';

/** Pop-up that is displayed when opening the privacy policy.
 *
 * `handleClose` is the function to close it again because it's open/closed state is
 * controlled by the containing element.
 *
 * Note: Do not translate the Impressum!
 */
export function PrivacyPolicyPopup ({handleClose}: {handleClose: () => void}) {
  let {t, i18n} = useTranslation()
  function content (lng = i18n.language) {
    const tt = i18n.getFixedT(lng);
    return <Trans t={tt} >
        <h2>Privacy Policy</h2>
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
          Marcus Zibrowius<br />
        Mathematisches Institut der Heinrich-Heine-Universität Düsseldorf<br />
        Universitätsstr. 1<br />
        40225 Düsseldorf<br />
        Germany<br />
        +49 211 81 13858<br />
        <a href="https://www.math.uni-duesseldorf.de/~zibrowius/">Contact Details</a><br />
        <a href="mailto:matvey.lorkish@hhu.de?subject=Lean4Game: <Your%20Question>">Technical Contact</a>
        </p>
      </Trans>
  }


  return <div className="privacy-policy modal-wrapper">
  <div className="modal-backdrop" onClick={handleClose} />
    <div className="modal">
      <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
        {i18n.language != 'en' && <>
          <p><i>(English version below)</i></p>
          {content()}
          <hr />
        </>}
        {content('en')}
    </div>
</div>
}

/** Pop-up that is displayed when opening the privacy policy.
 *
 * `handleClose` is the function to close it again because it's open/closed state is
 * controlled by the containing element.
 *
 * Note: Do not translate the Impressum!
 */
export function ImpressumPopup ({handleClose}: {handleClose: () => void}) {
  let {t, i18n} = useTranslation()

  function content (lng = i18n.language) {
    const tt = i18n.getFixedT(lng);
    return <Trans t={tt} >
        <h2>Impressum</h2>
        <p>
          <strong>Contact:</strong><br />
          Marcus Zibrowius, Jon Eugster<br />
          Mathematisches Institut der Heinrich-Heine-Universität Düsseldorf<br />
          Universitätsstr. 1<br />
          40225 Düsseldorf<br />
          Germany<br />
          +49 211 81-14690<br />
          <a href="https://www.math.hhu.de/en/lehrstuehle-/-personen-/-ansprechpartner/innen/lehrstuehle-des-mathematischen-instituts/lehrstuhl-fuer-algebraische-geometrie/team">Contact Details</a>
        </p>
        <p>
          <strong>Legal form:</strong><br />
          The Heinrich Heine University Düsseldorf is a corporation under public law. It is legally represented by the Rector Prof. Dr. Anja Steinbeck. The responsible supervisory authority is the Ministry of Culture and Science of North Rhine-Westphalia, Völklinger Straße 49, 40221 Düsseldorf.
        </p>
        <p>
          <strong>VAT identification number:</strong><br />
            according to §27a Sales Tax Act<br />
            DE 811222416
        </p>
        <p><a href="https://www.hhu.de/impressum" target="_blank">Impressum HHU</a></p>
      </Trans>
  }

  return <div className="privacy-policy modal-wrapper">
  <div className="modal-backdrop" onClick={handleClose} />
    <div className="modal">
      <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
        {i18n.language != 'en' && <>
          <p><i>(English version below)</i></p>
          {content()}
          <hr />
        </>}
        {content('en')}
    </div>
</div>
}
