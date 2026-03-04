#!/usr/bin/env sh
set -eu

out="DASHI/Everything.agda"

printf 'module DASHI.Everything where\n\n' > "$out"

# Find all .agda files, excluding the generated file itself and build/.git/.agda dirs.
find . -type f -name "*.agda" \
  ! -path "./DASHI/Everything.agda" \
  ! -path "./build/*" \
  ! -path "./.git/*" \
  ! -path "./.agda/*" \
  | sort \
  | sed -e 's#^\./##' -e 's#/\|\\#.#g' -e 's/\.agda$//' -e 's/^/import /' \
  >> "$out"
