#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

OWNER=DASHI/Education/DigitalESDAdaptiveScreeningControllerExact.agda
REG=DASHI/Education/DigitalESDAdaptiveScreeningControllerRegression.agda
AGG=DASHI/EverythingDigitalESDReciprocalBraid.agda
PY=scripts/compile_digital_esd_adaptive_screening.py

for f in "$OWNER" "$REG" "$AGG" "$PY"; do
  [[ -f "$f" ]] || { echo "missing: $f" >&2; exit 1; }
done

grep -q '^import DASHI.Education.DigitalESDAdaptiveScreeningControllerExact$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDAdaptiveScreeningControllerRegression$' "$AGG"

python3 -m py_compile "$PY"

if grep -nE '\\{![^}]*!\\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)' "$OWNER" "$REG"; then
  echo "unsafe/incomplete Agda surface detected" >&2
  exit 1
fi

echo "digital-esd adaptive screening static checks: PASS"
