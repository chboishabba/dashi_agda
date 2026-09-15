#!/usr/bin/env bash
set -euo pipefail
ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Wikimedia/IbrahimMonster236BMcKayThompsonNormalizationInvariantOEISExact.agda"
[[ -f "$OWNER" ]] || { echo "missing owner: $OWNER" >&2; exit 1; }
required=(
  "record McKayThompsonNormalizationFamily"
  "A007246"
  "A007191"
  "A045479"
  "A035099"
  "A007244"
  "A030182"
  "A045481"
  "A007255"
  "A045485"
  "A121665"
  "qOneCoefficientIsNormalizationInvariant"
  "constantTermIsNormalizationDependent"
  "weightTwoTraceComesFromQOneCoefficient"
  "normalizationVariantDoesNotCreateSameSourceObject"
  "normalizationInvariantTraceDoesNotCreateClassPowerMap"
  "currentNormalizationInvariantOEISFrontier"
)
for needle in "${required[@]}"; do
  grep -Fq "$needle" "$OWNER" || { echo "missing Monster 2B/3B/6B normalization marker: $needle" >&2; exit 1; }
done
echo "monster 2B/3B/6B McKay-Thompson normalization-invariant OEIS check: ok"
