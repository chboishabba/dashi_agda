#!/usr/bin/env bash
set -euo pipefail

FILE="DASHI/Biology/BioacousticFlySIUnitSnowballParetoBidiExact.agda"
[[ -f "$FILE" ]] || { echo "missing $FILE" >&2; exit 1; }

grep -q 'import DASHI.Physics.Units.SI as SI' "$FILE"
grep -q 'unitSemanticsDebt' "$FILE"
grep -q 'seven explicitly declared debt/risk/cost/unit axes' "$FILE"
grep -q 'protocolRateUnit = SI.hertz' "$FILE"
grep -q 'protocolTimeUnit = SI.second' "$FILE"
grep -q 'embeddingCoordinatesDimensionless' "$FILE"
grep -q 'microscopyLengthScale = SI.microScale' "$FILE"
grep -q 'unitsDoNotCreateSameObjectIdentity' "$FILE"
grep -q 'unitsDoNotCreateCausalAuthority' "$FILE"

echo "bioacoustic/fly SI-unit static contract: PASS"
