# Lean 4 Game

This is the source code for a Lean 4 game platform hosted at [adam.math.hhu.de](https://adam.math.hhu.de).

The project is based on ideas from the [Lean Game Maker](https://github.com/mpedramfar/Lean-game-maker) and the [Natural Number Game
(NNG)](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/)
of Kevin Buzzard and Mohammad Pedramfar.
The project is based on Patrick Massot's prototype: [NNG4](https://github.com/PatrickMassot/NNG4).

## Creating a Game

Please follow the tutorial [Creating a Game](doc/create_game.md).
In particular step 5 thereof explains [How to Run Games Locally](doc/running_locally.md).

### Publishing a Game

We encourage anybody to have games hosted on our [Lean Game Server](https://adam.math.hhu.de) for anybody to play. For that you simply need to contact us with the link to your game repo. We are also happy to add work-in-progress games and games in any language.

For example, you can [Contact Jon on Zulip](https://leanprover.zulipchat.com/#narrow/dm/385895-Jon-Eugster). Or [via Email](https://www.math.hhu.de/en/lehrstuehle-/-personen-/-ansprechpartner/innen/lehrstuehle-des-mathematischen-instituts/lehrstuhl-fuer-algebraische-geometrie/team/jon-eugster).

## Documentation

The documentation for the game engine itself is still missing, but there is [Creating a Game](doc/create_game.md) explaining the API to create a game.

Some documentation:

- [NPM Scripts](doc/npm_scripts.md)
- [Old documentation](doc/DOCUMENTATION.md)

## Contributing

Contributions to `lean4game` are always welcome!

## Security

Providing the use access to a Lean instance running on the server is a severe security risk. That is why we start the Lean server with bubblewrap.
