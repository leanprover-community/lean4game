# Homepage announcements

Copy `announcements.example.json` to `announcements.json` in the repository root,
or set `ANNOUNCEMENTS_FILE` to an absolute path. The runtime file is ignored by
Git. A missing file or an empty `announcements` array shows no notices.

The relay reads the file on every `GET /data/announcements` request. The homepage
refreshes notices every minute, so edits require no rebuild or restart.

Each announcement requires:

- `id`: a unique, nonempty string.
- `title` and `message`: objects mapping language codes to nonempty text. English
  (`en`) is required as a fallback. Messages support Markdown; raw HTML is not
  rendered.

Optional fields:

- `priority`: a number, default `0`. Higher values appear first; ties retain file
  order.
- `startsAt`: start time, inclusive.
- `endsAt`: end time, exclusive.

Dates must be ISO timestamps with an explicit timezone. Omit both dates to keep
an announcement active indefinitely. Translations use the selected language,
then its base language, then English.

Validate the file before publishing changes. Invalid JSON or entries produce
HTTP 503 and a relay log entry. Open pages retain their previous notices during
failures, removing expired ones on the next refresh attempt. To avoid partially
written files, write a replacement file and rename it over the runtime file.
