# Importing games

There is an mechanism to import games into your server. In order to use this mechanism, you need
to create a [Github Access token](https://docs.github.com/en/authentication/keeping-your-account-and-data-secure/managing-your-personal-access-tokens). A fine-grained access token with only reading rights for public
repos will suffice.

You need to set the environment variables `LEAN4GAME_GITHUB_USER` and `LEAN4GAME_GITHUB_TOKEN`
with your user name and access token.

Then you can call:

> https://{website}/import/trigger/{owner}/{repo}

where you replace:
- website: The website your server runs on, e.g. `localhost:3000`
- owner, repo: The owner and repository name of the game you want to load from github.

 will trigger to download the latest version of your game from github onto your server.
 Once this import reports "Done", you should be able to play your game under:

> https://{website}/#/g/{owner}/{repo}

## data management
Everything downloaded remains in the folder `lean4game/games`.
the subfolder `tmp` contains downloaded artifacts and can be deleted without loss.
The other folders should only contain the built lean-games, sorted by owner and repo.
