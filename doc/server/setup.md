# Setup

How to run Lean Games on a server: pm2 keeps the Node server running on `127.0.0.1:8000`,
nginx serves the built client and forwards the API to the Node server.

These instructions assume a Linux server with the `apt` package manager; the steps are
analogous for other distributions.

## Install the dependencies

Install Node with `nvm`, see the version in the [README](../../README.md):

```bash
curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.2/install.sh | bash
source ~/.bashrc
nvm install 26
```

Install `pm2`, which keeps the Node server running:

```bash
npm install pm2 -g
```

Install `elan`, which manages the Lean versions. The import of a game installs the Lean
version the game needs.

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source $HOME/.elan/env
```

Imports also need `unzip`:

```bash
sudo apt install unzip
```

## Install bubblewrap (bwrap)

```bash
sudo apt-get install bubblewrap
```

### AppArmor (Ubuntu 24.04 and newer)

bubblewrap creates a user namespace (`--unshare-user`) to build the sandbox without root.
Since 24.04, Ubuntu only allows this to programs whose AppArmor profile permits it, and the
`bubblewrap` package doesn't come with one. Without a profile, starting a game fails with an
error like `bwrap: setting up uid map: Permission denied`.

Add a profile that allows `/usr/bin/bwrap`, and only it, to create user namespaces:

```bash
sudo tee /etc/apparmor.d/bwrap > /dev/null << 'EOF'
abi <abi/4.0>,
include <tunables/global>

profile bwrap /usr/bin/bwrap flags=(unconfined) {
  userns,

  # Site-specific additions and overrides. See local/README for details.
  include if exists <local/bwrap>
}
EOF
sudo systemctl reload apparmor
```

`flags=(unconfined)` adds no further restrictions; `userns,` is the permission that matters.
Check that the sandbox works:

```bash
bwrap --unshare-user --ro-bind / / true && echo ok
```

The CI tests in production mode on Linux set up the same profile.

## nginx

nginx handles HTTPS and anonymized logging and forwards every request to the Node server. The
Node server answers the API and, in production, also serves the built client: `npm run build`
writes it to `client/dist` (see `server/src/client.ts`). Vite is only used to build the client
and doesn't run in production. As nginx doesn't know about individual paths, its configuration
doesn't need to change when endpoints are added or removed.

Install nginx:

```bash
sudo apt update
sudo apt install nginx
```

The configuration is in [`deploy/nginx/leangame.conf`](../../deploy/nginx/leangame.conf). Adjust
`server_name` and the certificate paths, then enable it:

```bash
sudo unlink /etc/nginx/sites-enabled/default
sudo ln -s /path/to/leangame/deploy/nginx/leangame.conf /etc/nginx/sites-enabled/leangame.conf
sudo nginx -t
sudo nginx -s reload
```

Linking the file from the repository keeps the server's configuration up to date with
`git pull`; reload nginx after it changed. Copy the file to `/etc/nginx/sites-available/`
instead if you need local changes.

Notes on the configuration:

- **Privacy**: the access log anonymizes IP addresses, the error log is disabled because it
  would contain them, and the client's IP address isn't forwarded to the Node server.
- **Timeouts**: nginx waits up to 3 minutes for the Node server, longer than a proof check may
  take (`LEAN_CHECK_TIMEOUT_MS`, 2 minutes by default).
- **Other sites**: the file contains the HTTP→HTTPS redirect as `default_server` and the `map`
  for anonymized IPs. If the server hosts further sites in other files, keep these only once.
- **Statistics**: to restrict `/stats` to certain addresses, uncomment the prepared `location`
  block.

The Node server should only be reachable through nginx, so `ecosystem.config.cjs` sets
`HOST=127.0.0.1`.

The Node server serves the client with suitable caching: the files in `client/dist/assets/`
have a hash in their name and are cached for a year; `index.html` is never cached, so a new
build is picked up immediately. Unknown paths outside `/api` and `/stats` get
`index.html`, so that reloading a page of the client works.

## Install leangame

Clone the repository with the HTTPS URL:

```bash
git clone https://github.com/leanprover-community/lean4game.git leangame
cd leangame
npm ci
npm run build
```

Fill in the environment variables in `ecosystem.config.cjs`, see [server.md](server.md#environment-variables)
and [importing games](#importing-games).

Moreover, adjust the configuration `server/config.json` to insert your server-specific details, see [server.md](server.md#configuration).

Start the server with pm2:

```bash
pm2 start ecosystem.config.cjs
```

Then the instance is available under the domain configured in nginx.

## Importing games

Games are imported from GitHub: the GitHub action of a game builds it and uploads it as an
artifact, which the server downloads.

For this, the server needs a
[fine-grained GitHub access token](https://docs.github.com/en/authentication/keeping-your-account-and-data-secure/managing-your-personal-access-tokens)
with the following properties:

- Expiration: choose "Custom" and select a day up to 365 days from today. (Note that you need
  to renew the token after a year.)
- Repository access: Public repositories (read-only)
- No further permissions. It should say "0 permissions for none of your repositories" and
  "0 account permissions".

Save the token after its generation, as you can only see it once, and set it as
`LEANGAME_GITHUB_TOKEN` together with your GitHub user name as `LEANGAME_GITHUB_USER` in
`ecosystem.config.cjs`.

Then a game can be imported on the page `https://{website}/import` by entering the owner
and the name of its repository. Once the import reports that it is done, the game can be
played at `https://{website}/g/{owner}/{repo}`. To list it on the landing page, add it to
`featuredGames` in the [configuration](server.md#configuration).

### Data management

The imported games are in the folder `server/games/` (see `GAMES_DIR`), sorted by owner and
repository. The subfolder `.import` contains the temporary files of running imports.

## Deploying an update

```bash
git pull
npm ci
npm run build
pm2 restart leangame
```

nginx doesn't need a reload.
