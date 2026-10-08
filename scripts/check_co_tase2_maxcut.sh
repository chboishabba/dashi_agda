#!/usr/bin/env bash
set -euo pipefail

python3 scripts/co_tase2_bloch_symmetry.py
python3 -m py_compile \
  scripts/co_tase2_bloch_symmetry.py \
  scripts/co_tase2_bns_operation_audit.py \
  scripts/co_tase2_arpes_ibw_ingest.py \
  scripts/co_tase2_arpes_peak_fit.py

if command -v agda >/dev/null 2>&1; then
  agda -i . -i /usr/share/agda-stdlib \
    DASHI/Physics/CondensedMatter/Everything.agda
else
  echo "AGDA-NOT-AVAILABLE: umbrella kernel receipt not produced" >&2
  exit 2
fi
