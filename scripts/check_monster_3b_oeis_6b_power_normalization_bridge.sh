#!/usr/bin/env bash
set -euo pipefail
ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Wikimedia/IbrahimMonster3BOEIS6BPowerNormalizationBridgeExact.agda"
PARENT="$ROOT/scripts/check_monster_3b_multiplicity_basis_linear_wrongtype.sh"
[[ -f "$OWNER" ]] || { echo "missing owner: $OWNER" >&2; exit 1; }
[[ -f "$PARENT" ]] || { echo "missing parent tranche: $PARENT" >&2; exit 1; }
required=(
  "A121665"
  "A007255"
  "Monster class 6B"
  "Monster class 3B"
  "sixBSquareLandsInThreeB"
  "a121665ConstantTwelve"
  "a007255NormalizedConstantZero"
  "sharedQCoefficientSeventyEight"
  "twelveIsNormalizationDependent"
  "sixBPowerRelationDoesNotCreateMultiplicityWeld"
  "seventyEightCoefficientDoesNotIdentifyMultiplicitySeventyEight"
  "normalizationTwelveDoesNotIdentifyMultiplicityTwelve"
  "oeis6BPowerNormalizationFrontier"
)
for needle in "${required[@]}"; do
  grep -Fq "$needle" "$OWNER" || { echo "missing 6B OEIS bridge marker: $needle" >&2; exit 1; }
done
grep -Fq 'check_monster_3b_oeis_6b_power_normalization_bridge.sh' "$PARENT" || {
  echo "parent Monster tranche does not chain 6B power-normalization boundary" >&2; exit 1;
}
echo "monster 3B OEIS 6B power-normalization check: ok"
