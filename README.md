# Lean 4 Game

This is the source code for the Lean Game Server hosted at [adam.math.hhu.de](https://adam.math.hhu.de).

## Creating a Game

Please follow the tutorial [Creating a Game](doc/create_game.md). In particular, the following steps may be of interest:

* Step 6: [How to Run Games Locally](doc/running_locally.md)
* Step 8: [How to Update an existing Game](doc/update_game.md)
* Step 10: [How to Publish a Game](doc/publish_game.md)
* [Troubleshooting](doc/troubleshoot.md)

## Documentation

The documentation is very much work in progress but the links below should be up-to-date:

### Game creation API

- [Creating a Game](doc/create_game.md): **the main document to consult**.
- [More about Hints](doc/hints.md): describes the `Hint` and `Branch` tactics.

### Frontend API

* [How to Run Games Locally](doc/running_locally.md): play a game on your computer
* [How to Update an existing Game](doc/update_game.md): update to a new lean version
* [How to Publish a Game](doc/publish_game.md): load your game to adam.math.hhu.de for others to play

### Backend

* [Server](doc/DOCUMENTATION.md): describes the server part (i.e. the content of `server/` and `relay/`).

### Hosting
* [How to host a lean4game instance yourself](doc/hosting.md): how to set up your own Lean Game Server

## Contributing

Contributions to `lean4game` are always welcome!

### Translation

We welcome translations of the game interface and of the various games hosted on the [Lean Game Server](https://adam.math.hhu.de) into different languages!  

* For translating the *interface*, please refer to [these instructions](doc/translation-interface.md).  
* For translating *individual games*, please contact the maintainers (see [table below](#contact)) and consult any game specific translation guidelines.  Our [generic guidlines](doc/translation-guide-for-game-translators.md) may give a rough indication of the steps involved.
* We also have some [guidelines for game maintainers](doc/translation-guide-for-game-maintainers.md) regarding translations.

## Security

Providing the use access to a Lean instance running on the server is a severe security risk. That is why we start the Lean server with bubblewrap.

## Contact

In case of technical problems with/outages of the server at `adam.math.hhu.de` please contact <a href="mailto:matvey.lorkish@hhu.de?subject=Lean4Game: <Your%20Question>">Matvey Lorkish</a>.

Bug reports and feature requests regarding the game interface should be filed on the [issues page](issues) of this repository.

For specific games on the [Lean Game Server](https://adam.math.hhu.de), please refer to the github repositories linked to below or contact the maintainers.

| Game/repository                                                                   | Maintainer                                              |
|-----------------------------------------------------------------------------------|---------------------------------------------------------|
| [Knights and Knaves](https://github.com/jadabouhawili/knightsandknaves-lean4game) | [Jad Abou Hawili](https://github.com/JadAbouHawili)     |
| [Linear Algebra Game](https://github.com/zrtmrh/linearalgebragame)                | [ZRTMRH](https://github.com/ZRTMRH)                     |
| [Logic Game](https://github.com/trequetrum/lean4game-logic)                       | [Trequetrum](https://github.com/Trequetrum)             |
| [Natural Number Game (NNG)](https://github.com/leanprover-community/nng4)         | [Kevin Buzzard](https://github.com/kbuzzard)            |
| [Real Analysis Game](https://github.com/alexkontorovich/realanalysisgame)         | [Alex Kontorovich](https://github.com/AlexKontorovich)  |
| [Reintroduction to Proofs](https://github.com/emilyriehl/reintroductiontoproofs)  | [Emily Riehl](https://github.com/emilyriehl)            |
| [Robo / Scribble](https://github.com/hhu-adam/robo)                               | [Marcus Zibrowius](https://github.com/TentativeConvert) |
| [Set Theory Game](https://github.com/djvelleman/stg4)                             | [Dan Velleman](https://github.com/djvelleman)


## Credits

The project has primarily been developed by Alexander Bentkamp and Jon Eugster.

It is based on ideas from the [Lean Game Maker](https://github.com/mpedramfar/Lean-game-maker) and the [Natural Number Game
(NNG)](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/)
by Kevin Buzzard and Mohammad Pedramfar, and on Patrick Massot's prototype: [NNG4](https://github.com/PatrickMassot/NNG4).
