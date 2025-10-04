
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

## Server capacity

If you would like to display the server capacity on the landing page,
you can create a file `lean4game/games/stats.csv` of the following form:

```
CPU,MEM
0.1,0.8
```

These numbers will be displayed on the landing page ("CPU: 10 % used" and "RAM: 80 % used").

If you only want one of the numbers, replace the number you don't want with `nan` (or anything
else which does not parse as number).

If you don't want to show either, simply do not create `stats.csv`

Use your own script or cronjob to update the CSV file as desired.
