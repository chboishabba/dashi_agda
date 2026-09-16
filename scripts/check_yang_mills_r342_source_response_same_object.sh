#!/usr/bin/env bash
set -euo pipefail

R342_ROOT="DASHI/Physics/YangMills/BalabanCMP116R281SourceResponseSameObjectRound342ValidationExact.agda"
R342_PRODUCTION="DASHI/Physics/YangMills/BalabanCMP116R281SourceResponseSameObjectRound342Exact.agda"
R343_ROOT="DASHI/Physics/YangMills/BalabanCMP116R281SelectedSourceUpperRound343ValidationExact.agda"
R343_PRODUCTION="DASHI/Physics/YangMills/BalabanCMP116R281SelectedSourceUpperRound343Exact.agda"

for path in "$R342_PRODUCTION" "$R342_ROOT" "$R343_PRODUCTION" "$R343_ROOT"; do
  test -f "$path"
done

# R342 WrongType / donor boundary remains fail-closed.
grep -q 'record SourceResponseSameObjectPayment' "$R342_PRODUCTION"
grep -q 'record CMP109CMP116SourceResponseIdentity' "$R342_PRODUCTION"
grep -q 'r321SameObjectBuildsB1AfterSourceIdentity' "$R342_PRODUCTION"
grep -q 'r321SameObjectCanFeedB1AfterSourceIdentity = true' "$R342_PRODUCTION"
grep -q 'r321CMP109DonorIsPreferredB1Route = false' "$R342_PRODUCTION"
grep -q 'directCMP116JResponseIsPreferredB1Route = true' "$R342_PRODUCTION"
grep -q 'cmp109PiIdentificationRequiredByPreferredB1 = false' "$R342_PRODUCTION"
grep -q 'cmp109PiIsDefinitionallyTwoJConnectedCumulant' "$R342_PRODUCTION"
grep -q 'round342SourceResponseSameObjectLevel = conditional' "$R342_PRODUCTION"
grep -q 'round342CMP109CMP116SourceIdentityLevel = conditional' "$R342_PRODUCTION"
grep -q 'round342EnvelopeCalibrationLevel = conditional' "$R342_PRODUCTION"

# R343 Pareto recut: the terminal mass-gap consumer needs only the selected
# response upper, not primitive equality with the abstract CMP116 magnitude.
grep -q 'record SelectedResponseSourceUpperApplication' "$R343_PRODUCTION"
grep -q 'selectedResponseBelowSourceEnvelope' "$R343_PRODUCTION"
grep -q 'sourceEnvelopeBelowSpectrumEnvelope' "$R343_PRODUCTION"
grep -q 'r341ApplicationBuildsR343' "$R343_PRODUCTION"
grep -q 'selectedSourceUpperBuildsSubgapUpper' "$R343_PRODUCTION"
grep -q 'sourceMagnitudeEqualityPrimitiveForMassGapConsumer = false' "$R343_PRODUCTION"
grep -q 'selectedResponseSourceUpperStillRequired = true' "$R343_PRODUCTION"
grep -q 'sourceEnvelopeCalibrationStillRequired = true' "$R343_PRODUCTION"
grep -q 'oldR341ApplicationCompilesToR343 = true' "$R343_PRODUCTION"
grep -q 'r343DoesNotRecoverSourceMagnitudeEquality = true' "$R343_PRODUCTION"
grep -q 'freshYMDecayEstimateIntroduced = false' "$R343_PRODUCTION"
grep -q 'clayPromotion = false' "$R343_PRODUCTION"
grep -q 'round343SelectedResponseSourceUpperLevel = conditional' "$R343_PRODUCTION"

if command -v agda >/dev/null 2>&1; then
  agda "$R342_ROOT"
  agda "$R343_ROOT"
else
  echo 'Agda executable unavailable; static R342/R343 contracts checked only.' >&2
  exit 2
fi
