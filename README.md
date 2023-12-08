# Lean 4 Game

This is the source code for a Lean 4 game platform hosted at [adam.math.hhu.de](https://adam.math.hhu.de).

## Creating a Game

Please follow the tutorial [Creating a Game](doc/create_game.md). In particular, the following steps might be of interest:

* Step 5: [How to Run Games Locally](doc/running_locally.md)
* Step 7: [How to Update an existing Game](doc/update_game.md)
* Step 8: [How to Publishing a Game](doc/publish_game.md)

### Publishing a Game

We encourage anybody to have games hosted on our [Lean Game Server](https://adam.math.hhu.de) for anybody to play.

You can simply load your game to this server yourself following [How to Publishing a Game](doc/publish_game.md). However, to be featured on the server's starting page, you will need to reach out to be added manually.

For example, you can [contact Jon on Zulip](https://leanprover.zulipchat.com/#narrow/dm/385895-Jon-Eugster). Or [via Email](https://www.math.hhu.de/en/lehrstuehle-/-personen-/-ansprechpartner/innen/lehrstuehle-des-mathematischen-instituts/lehrstuhl-fuer-algebraische-geometrie/team/jon-eugster).

## Documentation

The main documentation is [Creating a Game](doc/create_game.md) which explains the API to a user who wants to create a game.

Some random documentation:

- [NPM Scripts](doc/npm_scripts.md)
- [Old documentation](doc/DOCUMENTATION.md)

## Contributing

Contributions to `lean4game` are always welcome!

## Security

Providing the use access to a Lean instance running on the server is a severe security risk. That is why we start the Lean server with bubblewrap.

## Credits

The project is based on ideas from the [Lean Game Maker](https://github.com/mpedramfar/Lean-game-maker) and the [Natural Number Game
(NNG)](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/)
by Kevin Buzzard and Mohammad Pedramfar.
The project is based on Patrick Massot's prototype: [NNG4](https://github.com/PatrickMassot/NNG4).
