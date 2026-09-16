#!/usr/bin/env bash
set -euo pipefail
ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Wikimedia/IbrahimMonster6BWeightTwoC6FourierOEISExact.agda"
PARENT="$ROOT/scripts/check_monster_3b_multiplicity_basis_linear_wrongtype.sh"
[[ -f "$OWNER" ]] || { echo "missing owner: $OWNER" >&2; exit 1; }
[[ -f "$PARENT" ]] || { echo "missing parent tranche: $PARENT" >&2; exit 1; }
required=(
  "A007255"
  "A007246"
  "sixBTraceWeightTwo"
  "threeBTraceWeightTwo"
  "twoBTraceWeightTwo"
  "traceVector19688478542765478"
  "record C6WeightTwoMultiplicitySpectrum"
  "32904"
  "32772"
  "32838"
  "32760"
  "dimensionEquation"
  "sixBTraceEquation"
  "threeBTraceEquation"
  "twoBTraceEquation"
  "IbrahimMonster236BMcKayThompsonNormalizationInvariantOEISExact"
  "IbrahimMonster6BCompleteReplicabilityPowerSnowballExact"
  "normalizationInvariantTraceBoundary"
  "replicabilityPowerBoundary"
  "normalizationInvariantTraceExtractionPaid"
  "wholeSeriesReplicabilityPowerRelationPaid"
  "c6SpectrumDoesNotCreateN3BMultiplicityWeld"
  "weightTwoC6FourierFrontier"
)
for needle in "${required[@]}"; do
  grep -Fq "$needle" "$OWNER" || { echo "missing 6B C6 Fourier marker: $needle" >&2; exit 1; }
done
grep -Fq 'check_monster_6b_weight_two_c6_fourier_oeis.sh' "$PARENT" || {
  echo "parent Monster tranche does not chain 6B C6 Fourier boundary" >&2; exit 1;
}
echo "monster 6B weight-two C6 Fourier OEIS check: ok"
