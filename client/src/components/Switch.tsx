import { twMerge } from 'tailwind-merge'

/** An on/off switch with a label to its right */
export function Switch({
  checked,
  onChange,
  label,
}: {
  checked: boolean
  onChange: (checked: boolean) => void
  label: string
}) {
  return (
    <label className="inline-flex cursor-pointer items-center gap-3">
      <input
        type="checkbox"
        role="switch"
        aria-checked={checked}
        className="peer sr-only"
        checked={checked}
        onChange={ev => onChange(ev.target.checked)}
      />
      <span
        className={twMerge(
          // the track
          'relative h-6 w-11 shrink-0 rounded-full bg-gray-300 transition-colors',
          'peer-checked:bg-primary peer-focus-visible:outline-2',
          'peer-focus-visible:outline-offset-2 peer-focus-visible:outline-primary',
          // the knob
          'after:absolute after:top-0.5 after:left-0.5 after:size-5 after:rounded-full',
          'after:bg-white after:shadow after:transition-transform',
          'peer-checked:after:translate-x-5',
        )}
      />
      {label}
    </label>
  )
}
