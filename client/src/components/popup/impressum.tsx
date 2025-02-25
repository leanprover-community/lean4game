import * as React from 'react'
import { Trans, useTranslation } from 'react-i18next';

/** Pop-up that is displayed when opening the privacy policy. */
export function ImpressumPopup () {
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
        <a href="https://www.math.hhu.de/lehrstuehle-/-personen-/-ansprechpartner/innen/lehrstuehle-des-mathematischen-instituts/lehrstuhl-fuer-algebraische-geometrie/team/prof-dr-marcus-zibrowius">Contact Details</a>
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

  return <>
    {i18n.language != 'en' && <>
      <p><i>(English version below)</i></p>
      {content()}
      <hr />
    </>}
    {content('en')}
  </>
}
