#!/usr/bin/env bash
set -euxo pipefail

rm -rf build/latex
scripts/generate-everything.sh
python scripts/gen_book.py
latexmk -xelatex -interaction=nonstopmode -halt-on-error -outdir=build/latex build/latex/Book.tex
