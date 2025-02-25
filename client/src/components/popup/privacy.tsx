import * as React from 'react'
import { Trans, useTranslation } from 'react-i18next';

/** Pop-up that is displayed when opening the privacy policy.
 *
 * Note: Do not translate the Impressum!
 */
export function PrivacyPolicyPopup () {
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
          <strong>Contact:</strong><br />
          Marcus Zibrowius, Jon Eugster<br />
          Mathematisches Institut der Heinrich-Heine-Universität Düsseldorf<br />
          Universitätsstr. 1<br />
          40225 Düsseldorf<br />
          Germany<br />
          +49 211 81-14690<br />
          <a href="https://www.math.hhu.de/lehrstuehle-/-personen-/-ansprechpartner/innen/lehrstuehle-des-mathematischen-instituts/lehrstuhl-fuer-algebraische-geometrie/team/prof-dr-marcus-zibrowius">Contact Details</a>
        </p>
      </Trans>
  }

  return <>
    {i18n.language != 'en' && <>
      <p><i>(English version below)</i></p>
      {content()}
      <hr />
    </>}
    {content('en')}
  </>
}
