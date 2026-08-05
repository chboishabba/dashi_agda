#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/YangMills/BalabanP33RationalQuaternionWilsonSecondVariationExact.agda
  DASHI/Physics/YangMills/BalabanP33LiteralGaugeConstraintSecondVariationExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalSU2HodgeCoercivityExact.agda
  DASHI/Physics/YangMills/BalabanP33OpenPeriodicBoundaryEnergyAuditExact.agda
  DASHI/Physics/YangMills/BalabanP33PeriodicFourDimensionalHodgeIdentityExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalFlatWilsonCurlIdentificationExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalPeriodicOpenReferenceBridgeExact.agda
  DASHI/Physics/YangMills/BalabanP33LiteralGaugeConstraintCancellationExact.agda
  DASHI/Physics/YangMills/BalabanP33WilsonSharpBudgetCoercivityExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonGaugeBoundaryCoercivityExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalRationalWilsonPlaquetteJetExact.agda
  DASHI/Physics/YangMills/BalabanP33LiteralPhysicalPerturbationAdapterExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound22Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round twenty-two contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

checks=(
  'BalabanP33RationalQuaternionWilsonSecondVariationExact.agda:fourFactorSecondVariationAtomCountExact'
  'BalabanP33RationalQuaternionWilsonSecondVariationExact.agda:fourLinkWilsonSecondVariationIsSixteenScalarAtoms'
  'BalabanP33RationalQuaternionWilsonSecondVariationExact.agda:flatPlaquetteWilsonIsCurlSquare'
  'BalabanP33LiteralGaugeConstraintSecondVariationExact.agda:plaquetteWilsonIsSixteenAtomSum'
  'BalabanP33LiteralGaugeConstraintSecondVariationExact.agda:wilsonSecondVariationIsPlaquetteAtomSum'
  'BalabanP33PhysicalSU2HodgeCoercivityExact.agda:physicalReferenceDifferencePoincare'
  'BalabanP33OpenPeriodicBoundaryEnergyAuditExact.agda:unitBoundaryPeriodicMinusOpen'
  'BalabanP33PeriodicFourDimensionalHodgeIdentityExact.agda:summationByParts'
  'BalabanP33PeriodicFourDimensionalHodgeIdentityExact.agda:mixedCrossIdentity'
  'BalabanP33PeriodicFourDimensionalHodgeIdentityExact.agda:periodicScalarHodgeIdentity'
  'BalabanP33PhysicalFlatWilsonCurlIdentificationExact.agda:flatWilsonEnergyIsPhysicalPeriodicCurl'
  'BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact.agda:flatGaugeSecondVariationIsPeriodicDivergence'
  'BalabanP33PhysicalPeriodicOpenReferenceBridgeExact.agda:physicalPeriodicGradientSplitsOpenAndBoundary'
  'BalabanP33PhysicalPeriodicOpenReferenceBridgeExact.agda:physicalFlatHodgeWithBoundary'
  'BalabanP33LiteralGaugeConstraintCancellationExact.agda:flatHodgeOldRemainderIsNegativeGauge'
  'BalabanP33LiteralGaugeConstraintCancellationExact.agda:literalHessianCoerciveFromWilsonGaugeHodgeDifference'
  'BalabanP33WilsonSharpBudgetCoercivityExact.agda:sharpWilsonGaugeBudgetExact'
  'BalabanP33WilsonSharpBudgetCoercivityExact.agda:coupledSignedLowerFromSeparateBudgets'
  'BalabanP33PhysicalWilsonGaugeBoundaryCoercivityExact.agda:coupledRemainderWithBoundaryExact'
  'BalabanP33PhysicalWilsonGaugeBoundaryCoercivityExact.agda:literalHessianCoerciveFromPhysicalWilsonGaugeDefects'
  'BalabanP33PhysicalRationalWilsonPlaquetteJetExact.agda:physicalWilsonSecondVariationIsSixteenAtomSum'
  'BalabanP33PhysicalRationalWilsonPlaquetteJetExact.agda:physicalWilsonDefectIsAtomDifference'
  'BalabanP33LiteralPhysicalPerturbationAdapterExact.agda:literalHessianCoerciveFromSamePhysicalPerturbation'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

# Provenance and scope discipline.
grep -q '10.1103/PhysRevD.10.2445' \
  DASHI/Physics/YangMills/BalabanP33RationalQuaternionWilsonSecondVariationExact.agda
grep -q '10.1007/BF01466594' \
  DASHI/Physics/YangMills/BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact.agda
grep -q '10.1007/BF01240355' \
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonGaugeBoundaryCoercivityExact.agda
grep -q 'former overmatched' \
  DASHI/Physics/YangMills/BalabanP33LiteralGaugeConstraintCancellationExact.agda
grep -q '1549/196608' \
  DASHI/Physics/YangMills/BalabanP33WilsonSharpBudgetCoercivityExact.agda
grep -q '4595/196608' \
  DASHI/Physics/YangMills/BalabanP33WilsonSharpBudgetCoercivityExact.agda
grep -q 'carrier mismatch' \
  DASHI/Physics/YangMills/BalabanP33RationalQuaternionWilsonSecondVariationExact.agda
grep -q 'boundary term is positive' \
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonGaugeBoundaryCoercivityExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound22Validation.agda
