
# Notes for Server maintainer

In order to set up the server to allow imports, one needs to create a
[Github Access token](https://docs.github.com/en/authentication/keeping-your-account-and-data-secure/managing-your-personal-access-tokens). A fine-grained access token with only reading rights for public
repos will suffice.

You need to set the environment variables `LEAN4GAME_GITHUB_USER` and `LEAN4GAME_GITHUB_TOKEN`
with your user name and access token. For example, you can set these in `ecosystem.config.cjs` if
you're using `pm2`

Then people can call:

> https://{website}/import/trigger/{owner}/{repo}

where you replace:
- website: The website your server runs on, e.g. `localhost:3000`
- owner, repo: The owner and repository name of the game you want to load from github.

 will trigger to download the latest version of your game from github onto your server.
 Once this import reports "Done", you should be able to play your game under:

> https://{website}/#/g/{owner}/{repo}

## Data management
Everything downloaded remains in the folder `lean4game/games`.
The subfolder `tmp` contains downloaded artifacts and can be deleted without loss.
The other folders should only contain the built lean-games, sorted by owner and repo.
