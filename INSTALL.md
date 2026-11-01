# Installing dashi-agda

`dashi-agda` is an Agda library. It can be consumed either through Agda's
native library registry or through the repo flake.

## Manual Agda Setup

Clone the repo with submodules:

```sh
git clone --recurse-submodules <dashi-agda-url>
cd dashi_agda
```

Register the library files with Agda by adding these paths to
`~/.agda/libraries`:

```text
/path/to/agda-stdlib/standard-library.agda-lib
/path/to/dashi_agda/dchott-agda.agda-lib
/path/to/dashi_agda/cubical/cubical.agda-lib
/path/to/dashi_agda/dashi-agda.agda-lib
```

The root `dchott-agda.agda-lib` file is a local wrapper for the flat
`DCHoTT-Agda/` submodule. Cubical already ships its own `cubical.agda-lib`.

Optionally add the library names to `~/.agda/defaults`:

```text
standard-library
dchott-agda
cubical-0.9
dashi-agda
```

Then check a DASHI consumer with:

```sh
agda -l dashi-agda MyConsumer.agda
```

For a direct smoke check:

```sh
agda -l dashi-agda DASHI/DCHoTT/All.agda
```

## Nix Setup

The flake pins source inputs for DCHoTT and Cubical and exposes package
surfaces for the local Agda libraries:

```sh
nix build .#dchott-agda --no-link
nix build .#cubical --no-link
nix build .#dashi-agda --no-link
nix build .#check --no-link
```

For an interactive environment:

```sh
nix develop
```

Inside the shell, use the same Agda library names:

```sh
agda -l dashi-agda DASHI/DCHoTT/All.agda
```

## Importing

Agda modules can import DASHI modules by their normal module names:

```agda
import DASHI.Everything
import DASHI.DCHoTT.All
```

The current aggregate validation target is:

```sh
timeout 300s agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Everything.agda
```

Use the named `-l dashi-agda` route for consumers, and the explicit include-path
route when reproducing the repo's historical aggregate check exactly.
