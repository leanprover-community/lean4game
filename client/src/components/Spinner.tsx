import { faSpinner } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'

/** A large loading spinner, centered in its parent, e.g. while a lazy component loads */
export function Spinner() {
  return (
    <div className="flex h-full items-center justify-center">
      <FontAwesomeIcon
        icon={faSpinner}
        spinPulse
        className="text-3xl text-primary"
      />
    </div>
  )
}
