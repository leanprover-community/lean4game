# Homepage announcements

Copy `announcements.example.json` to `announcements.json` in the repository root.
The runtime file is ignored by Git and is outside `client/dist`, so client builds
do not overwrite it. A missing file or `{"announcements": []}` shows no notices.
The example file is a template, not an automatic fallback.

The relay reads the runtime file for every `GET /data/announcements` request.
The homepage loads notices immediately and refreshes them every minute. Edits
take effect on a page reload or the next refresh without a build or restart.

Each announcement needs a unique `id`, a `title` object, and a `message` object.
Both objects must include nonempty English (`en`) text. Add other language codes
as needed; the visitor's selected language is used, with a base language and
English fallback. Messages support Markdown links and formatting through the
existing Markdown component. Raw HTML is not rendered.

Optional fields:

- `priority`: a number, default `0`. Higher priorities appear first. Equal
  priorities retain their order in the file.
- `startsAt`: when the notice starts appearing, inclusive.
- `endsAt`: when it stops appearing, exclusive.

Omitting both dates keeps a notice active indefinitely. Dates must be ISO
timestamps with an explicit timezone (`Z` or an offset such as `+02:00`). They
control the notice's display period; describe the actual downtime in the message.
For example, add this entry to the array and replace the dates before use:

```json
{
  "id": "scheduled-maintenance",
  "priority": 100,
  "startsAt": "2026-10-05T12:00:00+02:00",
  "endsAt": "2026-10-12T18:00:00+02:00",
  "title": {
    "en": "Scheduled maintenance",
    "de": "Geplante Wartung"
  },
  "message": {
    "en": "The server will be unavailable on 12 October from 14:00 to 16:00 CEST.",
    "de": "Der Server ist am 12. Oktober von 14:00 bis 16:00 Uhr MESZ nicht erreichbar."
  }
}
```

## Local testing

From the repository root, run these in separate terminals:

```sh
npm run start:relay
```

```sh
npm run start:client
```

Open `http://localhost:3000/`. No Lean rebuild is needed just to test notices.
Check the endpoint with `curl -i http://localhost:3000/data/announcements`.
Add a second entry with a higher priority to check ordering. Set an end date in
the past to hide an entry, and switch the homepage language to test translations.
Remove a notice by deleting its entry; use an empty array to remove all notices.

## Deployment

Deploy the client and relay code once, build both, and restart the relay. Then
create the instance's `announcements.json`. Future edits only change that file.
For a different location, set `ANNOUNCEMENTS_FILE` to an absolute path before
starting the relay. The default location is resolved from the relay module, so
it works even when the process starts in the `relay/` workspace.

Check JSON syntax before replacing the file:

```sh
node -e 'JSON.parse(require("node:fs").readFileSync("announcements.json", "utf8")); console.log("Valid JSON")'
```

For live updates, prepare a file in the same directory and rename it over the
runtime file once valid. This avoids requests reading a partially written file.
Invalid JSON or invalid entries produce HTTP 503 and a relay log entry. On a
temporary failure, an open page keeps its last notices until a successful refresh,
removing expired ones at the next refresh attempt. A new page shows no notices
until loading succeeds. Both the endpoint and the client disable response caching.

Publish downtime notices in advance. A stopped relay cannot serve the homepage;
a notice visible during the outage itself requires a separate reverse proxy
maintenance page or external status page.
