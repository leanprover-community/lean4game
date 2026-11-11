# Client

This document describes features of the frontend/client side.

## URL

You can add `?lang=de` at the end of the URL to specify the language that should be set. This
will change the user's preferred language to the one specified.

### Environment variables

These are read by Vite, so they apply to `npm start` / `npm run start:client` and, for
`VITE_…`, at build time (`npm run build`): changing them later requires a new build.

| Name                           | Type             | Description                                                                        | Default |
| ------------------------------ | ---------------- | ---------------------------------------------------------------------------------- | ------- |
| `CLIENT_PORT`                  | number           | port of Vite's development server. It forwards `/api` to the Node server on `PORT` | `3000`  |
| `VITE_CLIENT_DEFAULT_LANGUAGE` | ISO language key | default language                                                                   | `en`    |
