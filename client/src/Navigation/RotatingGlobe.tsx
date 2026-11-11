import {
  faGlobeAfrica,
  faGlobeAmericas,
  faGlobeAsia,
  faGlobeEurope,
  faGlobeOceania,
} from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'

function getGlobeIcon(timezone: string) {
  if (!timezone) return faGlobeEurope

  if (timezone.startsWith('Africa')) return faGlobeAfrica
  if (timezone.startsWith('America')) return faGlobeAmericas
  if (timezone.startsWith('Europe')) return faGlobeEurope
  if (timezone.startsWith('Asia')) return faGlobeAsia
  if (timezone.startsWith('Australia') || timezone.startsWith('Pacific'))
    return faGlobeOceania
  return faGlobeEurope
}

/** Globe Icon, rotated to fit the user's timezone */
export default function RotatingGlobe() {
  const timezone = Intl.DateTimeFormat().resolvedOptions().timeZone
  const icon = getGlobeIcon(timezone)

  return <FontAwesomeIcon icon={icon} />
}
