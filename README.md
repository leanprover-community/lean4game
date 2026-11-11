[![Lean](https://img.shields.io/badge/Lean-v4.35.0-blue)](https://github.com/hhu-adam/leangame/blob/main/server/lean/lean-toolchain)
[![Node](https://img.shields.io/badge/Node-26-339933?logo=nodedotjs&logoColor=white)](https://nodejs.org)
[![Live](https://img.shields.io/badge/live-adam.math.hhu.de-brightgreen)](https://adam.math.hhu.de)
[![GitHub license](https://img.shields.io/badge/License-GPL_3.0-blue.svg)](https://github.com/hhu-adam/leangame/blob/main/LICENSE)
[![ci status](https://github.com/hhu-adam/leangame/actions/workflows/test.yml/badge.svg)](https://github.com/hhu-adam/leangame/actions/workflows/test.yml)

# Lean Games

This is the source code for the Lean Game Server hosted at [adam.math.hhu.de](https://adam.math.hhu.de).

## Creating a Game

Please follow the tutorial [Creating a Game](doc/game/create_game.md). In particular, the following steps may be of interest:

- Step 6: [How to Run Games Locally](doc/game/running_locally.md)
- Step 8: [How to Update an existing Game](doc/game/update_game.md)
- Step 10: [How to Publish a Game](doc/game/publish_game.md)

## Documentation

- [Creating a New Game](doc/game/create_game.md)
  - [Running games locally](doc/game/running_locally.md)
  - [Setup for every Lean file/level](doc/game/environment.md)
  - [Writing exercises](doc/game/writing_exercises.md)
  - [Hints](doc/game/hints.md)
  - [Styling the game with Markdown](doc/game/markdown.md)
  - [LaTeX in games](doc/game/latex.md)
  - [Translations: the game maintainer's point of view](doc/game/translation-guide-for-game-maintainers.md)
  - [Translations: guide for translators](doc/game/translation-guide-for-game-translators.md)
- Maintaining a Game
  - [Publishing a game](doc/game/publish_game.md)
  - [Updating a game](doc/game/update_game.md)
  - [Refactoring a game](doc/game/refactoring.md)
- [Server](doc/server/server.md)
  - [API](doc/server/api.md)
  - [Setup on a server](doc/server/setup.md)
  - [Statistics](doc/server/stats.md)
- [Client](doc/client/client.md)
  - [Translation of the game interface](doc/client/translation-interface.md)
- [Development](doc/development.md)

## Security

Providing the use access to a Lean instance running on the server is a severe security risk. That is why we start the Lean server with bubblewrap.

For security concerns, please use the github feature under "Security and quality" to report them, alternatively contact us directly.

## Contributing

Contributions to `lean4game` are always welcome!

- [Development Instructions](./doc/development.md)

### Translation

We welcome translations of the game interface and of the various games hosted on the [Lean Game Server](https://adam.math.hhu.de) into different languages!

- For translating the _interface_, please refer to [these instructions](doc/client/translation-interface.md).
- For translating _individual games_, please contact the maintainers (see [table below](#contact)) and consult any game specific translation guidelines. Our [generic guidelines](doc/game/translation-guide-for-game-translators.md) may give a rough indication of the steps involved.
- We also have some [guidelines for game maintainers](doc/game/translation-guide-for-game-maintainers.md) regarding translations.

## Licencing

The overall project is licensed under GPLv3 as set out in the file `LICENSE`.

The used images of "Robo", the little android, are licensed under CC BY 4.0, as set out in `licenses/LICENSE_ROBO_IMAGES_CC_BY`.
See the source repository https://github.com/hhu-adam/Robo-Images for more details about the images.

Further, some Lean snippets have been copied and modified from `lean4`, `batteries`, or `mathlib4` under Apache 2.0 licenses
of these projects, which are included under `licenses/`. The files with reused code are marked and contain the relevant
copyright information.

## Contact

In case of a server outage at `adam.math.hhu.de` please open an [issue](issues) and/or contact us by <a href="mailto:adam@math.hhu.de?subject=Server Outage">email</a>. Bug reports and feature requests regarding the game interface should be filed on the [issues page](issues) of this repository. For specific games on the [Lean Game Server](https://adam.math.hhu.de), please refer to the github repositories linked to below or contact the maintainers.

| Game/repository                                                                   | Maintainer                                              |
| --------------------------------------------------------------------------------- | ------------------------------------------------------- |
| [Knights and Knaves](https://github.com/jadabouhawili/knightsandknaves-lean4game) | [Jad Abou Hawili](https://github.com/JadAbouHawili)     |
| [Linear Algebra Game](https://github.com/zrtmrh/linearalgebragame)                | [ZRTMRH](https://github.com/ZRTMRH)                     |
| [Logic Game](https://github.com/trequetrum/lean4game-logic)                       | [Trequetrum](https://github.com/Trequetrum)             |
| [Natural Number Game (NNG)](https://github.com/leanprover-community/nng4)         | [Kevin Buzzard](https://github.com/kbuzzard)            |
| [Real Analysis Game](https://github.com/alexkontorovich/realanalysisgame)         | [Alex Kontorovich](https://github.com/AlexKontorovich)  |
| [Reintroduction to Proofs](https://github.com/emilyriehl/reintroductiontoproofs)  | [Emily Riehl](https://github.com/emilyriehl)            |
| [Robo / Scribble](https://github.com/hhu-adam/robo)                               | [Marcus Zibrowius](https://github.com/TentativeConvert) |
| [Set Theory Game](https://github.com/djvelleman/stg4)                             | [Dan Velleman](https://github.com/djvelleman)           |
| [Number Theory Game](https://github.com/k88-b/numbertheorygame)                   | [Konstantin Belyanin](https://github.com/k88-b)         |

## Credits

Developed by: Alexander Bentkamp, Jon Eugster, Marcus Zibrowius

Special thanks to several student assistants at [HHU](https://www.math.hhu.de) for contributing to this project

- It is based on ideas from the [Lean Game Maker](https://github.com/mpedramfar/Lean-game-maker) and the [Natural Number Game
  (NNG)](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/) by Kevin Buzzard and Mohammad Pedramfar
- An early prototype by Patrick Massot inspired the first draft of this project
- Parts of the unicode abbreviation feature were inspired by [@leanprover/unicode-input-component](https://www.npmjs.com/package/@leanprover/unicode-input-component).

### Translations

We are greatful for the work of many translators helping us to bring this learning
ressource to different languages:

- Andrii Kurdiumov: ukrainian
- Arnaud Bodin: french
- Bulhwi Cha: korean
- Federico Dal Pio Luogo: italian
- Luís Felipe Marques: portugese
- Violeta Hernández Palacios: spanish
- WangZhihong (Rex): chinese
- `JiechengZhao`: chinese
- `miguelmarco`: spanish

This list is likely incomplete.
If you contributed and your name is not on this list yet, please open a PR!
