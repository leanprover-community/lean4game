[![Lean](https://img.shields.io/badge/Lean-v4.35.0-blue)](https://github.com/hhu-adam/leangame/blob/main/server/lean/lean-toolchain)
[![Node](https://img.shields.io/badge/Node-26-339933?logo=nodedotjs&logoColor=white)](https://nodejs.org)
[![Live](https://img.shields.io/badge/live-adam.math.hhu.de-brightgreen)](https://adam.math.hhu.de)
[![GitHub license](https://img.shields.io/badge/License-GPL_3.0-blue.svg)](https://github.com/hhu-adam/leangame/blob/main/LICENSE)
[![ci status](https://github.com/hhu-adam/leangame/actions/workflows/test.yml/badge.svg)](https://github.com/hhu-adam/leangame/actions/workflows/test.yml)

# Lean Games

Reimplementation of lean4game with a better backend.

THIS IS WORK-IN-PROGRESS, NOT READY TO BE USED. Will be combined with leanprover-community/lean4game once it's ready.

## Security

Providing the use access to a Lean instance running on the server is a severe security risk. That is why we start the Lean server with bubblewrap.

## Contributing

TODO

- [Development Instructions](./doc/development.md)

## Licencing

The overall project is licensed under GPLv3 as set out in the file `LICENSE`.

The used images of "Robo", the little android, are licensed under CC BY 4.0, as set out in `licenses/LICENSE_ROBO_IMAGES_CC_BY`.
See the source repository https://github.com/hhu-adam/Robo-Images for more details about the images.

Further, some Lean snippets have been copied and modified from `lean4`, `batteries`, or `mathlib4` under Apache 2.0 licenses
of these projects, which are included under `licenses/`. The files with reused code are marked and contain the relevant
copyright information.

## Credits

Developed by: Alexander Bentkamp, Jon Eugster, Marcus Zibrowius

- An early prototype by Patrick Massot inspired the first draft of this project
- Parts of the unicode abbreviation feature were inspired by [@leanprover/unicode-input-component](https://www.npmjs.com/package/@leanprover/unicode-input-component).
