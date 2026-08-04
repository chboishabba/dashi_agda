#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/YangMills/BalabanBishopConfiguredTermIdentificationExact.agda
  DASHI/Physics/YangMills/BalabanBishopFullHalfBallParityChartExact.agda
  DASHI/Physics/YangMills/BalabanStepVPolynomialDirectRatioExact.agda
  DASHI/Physics/YangMills/BalabanP06PeriodicSupportBridgeExact.agda
  DASHI/Physics/YangMills/BalabanP06DiameterComplexityAuditExact.agda
  DASHI/Physics/YangMills/BalabanP11LightweightCanonicalPaymentExact.agda
  DASHI/Physics/YangMills/BalabanP33P10Gate4DependencySpineExact.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound11ExactCutset.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound11SourceAudit.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound11Ledger.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound11Receipt.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound11LightValidation.agda
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerSubmissionRound11Advance.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}' "${files[@]}"; then
  echo "round-eleven tranche contains an explicit postulate or hole" >&2
  exit 1
fi

# Exact Bishop and Step-V reducers introduced in this tranche.
grep -q 'configuredConcreteTermIdentification' \
  DASHI/Physics/YangMills/BalabanBishopConfiguredTermIdentificationExact.agda
grep -q 'orientedFullHalfBallBrackets' \
  DASHI/Physics/YangMills/BalabanBishopFullHalfBallParityChartExact.agda
grep -q 'reflectedNegativeHalfBallChart' \
  DASHI/Physics/YangMills/BalabanBishopFullHalfBallParityChartExact.agda
grep -q 'eventualTailDominationFromDirectRatio' \
  DASHI/Physics/YangMills/BalabanStepVPolynomialDirectRatioExact.agda
grep -q 'polynomialWeightedBoundFromDirectRatio' \
  DASHI/Physics/YangMills/BalabanStepVPolynomialDirectRatioExact.agda

# P06/P11 and physical dependency reducers.
grep -q 'periodicPhysicalPolymerSupportModel' \
  DASHI/Physics/YangMills/BalabanP06PeriodicSupportBridgeExact.agda
grep -q 'periodicConcreteBoundedDegreeEight' \
  DASHI/Physics/YangMills/BalabanP06PeriodicSupportBridgeExact.agda
grep -q 'superlinearFamilyRefutesUniformLinearDiameterBound' \
  DASHI/Physics/YangMills/BalabanP06DiameterComplexityAuditExact.agda
grep -q 'p11LightweightCanonicalReceipt' \
  DASHI/Physics/YangMills/BalabanP11LightweightCanonicalPaymentExact.agda
grep -q 'canonicalAnimalConstantFromLightweightReceipt' \
  DASHI/Physics/YangMills/BalabanP11LightweightCanonicalPaymentExact.agda
grep -q 'record P33CoerciveInversePackage' \
  DASHI/Physics/YangMills/BalabanP33P10Gate4DependencySpineExact.agda
grep -q 'record Gate4SevenPackageSpine' \
  DASHI/Physics/YangMills/BalabanP33P10Gate4DependencySpineExact.agda

# Source provenance and fail-closed accounting.
grep -q '10.1007/BF01211762' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound11SourceAudit.agda
grep -q '10.1007/BF01215753' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound11SourceAudit.agda
grep -q '10.1063/1.4821275' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound11SourceAudit.agda
grep -q 'configuredTermIdentificationReducedToDefinitions = true' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound11Receipt.agda
grep -q 'configuredTermDefinitionsDischarged = false' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound11Receipt.agda
grep -q 'orientedFullHalfBallChartReducerDischarged = true' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound11Receipt.agda
grep -q 'constructiveSignChartSelectionDischarged = false' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound11Receipt.agda
grep -q 'logarithmBackendRequiredForPolynomialAbsorption = false' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound11Receipt.agda
grep -q 'unrestrictedLinearDiameterInferenceRejected = true' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound11Receipt.agda
grep -q 'lightweightP11CanonicalConstantWired = true' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound11Receipt.agda
grep -q 'p11PhysicalStartupActivityNeighbourhoodDischarged = false' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound11Receipt.agda
grep -q 'continuumOSAndSIMassGapDischarged = false' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound11Receipt.agda
grep -q 'round11FocusedRootAccepted' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound11LightValidation.agda

roots=(
  DASHI/Physics/YangMills/BalabanBishopConfiguredTermIdentificationExact.agda
  DASHI/Physics/YangMills/BalabanBishopFullHalfBallParityChartExact.agda
  DASHI/Physics/YangMills/BalabanStepVPolynomialDirectRatioExact.agda
  DASHI/Physics/YangMills/BalabanP06PeriodicSupportBridgeExact.agda
  DASHI/Physics/YangMills/BalabanP06DiameterComplexityAuditExact.agda
  DASHI/Physics/YangMills/BalabanP11LightweightCanonicalPaymentExact.agda
  DASHI/Physics/YangMills/BalabanP33P10Gate4DependencySpineExact.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound11LightValidation.agda
)

for root_file in "${roots[@]}"; do
  scripts/run_agda29_parallel_check.sh "$root_file"
done
