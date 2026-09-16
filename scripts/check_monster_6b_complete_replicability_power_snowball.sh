#!/usr/bin/env bash
set -euo pipefail
ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Wikimedia/IbrahimMonster6BCompleteReplicabilityPowerSnowballExact.agda"
[[ -f "$OWNER" ]] || { echo "missing owner: $OWNER" >&2; exit 1; }
required=(
  "10.1080/00927879408825127"
  "10.1090/crmp/047/12"
  "A007255"
  "A007244"
  "A007246"
  "record Monster6BReplicabilityPowerReceipt"
  "secondReplicateIsThreeB"
  "thirdReplicateIsTwoB"
  "replicabilityExtendsPastWeightTwoTrace"
  "replicabilityDoesNotCreateLiteralVOASameObject"
  "replicateTargetDoesNotCreateMultiplicityIntertwiner"
  "currentMonster6BReplicabilityFrontier"
)
for needle in "${required[@]}"; do
  grep -Fq "$needle" "$OWNER" || { echo "missing 6B replicability marker: $needle" >&2; exit 1; }
done
echo "monster 6B complete replicability power snowball check: ok"
