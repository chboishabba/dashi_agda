#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

python3 scripts/check_ym_clay_frontier.py
python3 scripts/check_ym_clay_literature_normalization.py
