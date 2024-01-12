# Publishing games

You can publish your game on the official [Lean Game Server](https://adam.math.hhu.de) in a few simple
steps.

## 1. Upload Game to github

First, you need your game in a public Github repository and make sure the github action has run.
You can check this by spotting the green checkmark on the start page, or by looking at the "Actions"
tab.

## 2. Import the game

You call the URL that's listed under "What's Next?" in the latest action run. Explicitely you call
the URL of the form

> adam.math.hhu.de/import/trigger/{USER}/{REPOSITORY}

where `{USER}` and `{REPOSITORY}` are replaced with the github user and repository name.

You should see a white screen which shows import updates and eventually reports "Done."

## 3. Play the game

Now you can immediately play the game at `adam.math.hhu.de/#/g/{USER}/{REPOSITORY}`!

## 4. Main page

Adding games to the main page happens manually by the server maintainers. Tell us if you want us
to add a tile for your game!

For example, you can [contact Jon on Zulip](https://leanprover.zulipchat.com/#narrow/dm/385895-Jon-Eugster). Or [via Email](https://www.math.hhu.de/en/lehrstuehle-/-personen-/-ansprechpartner/innen/lehrstuehle-des-mathematischen-instituts/lehrstuhl-fuer-algebraische-geometrie/team/jon-eugster).
