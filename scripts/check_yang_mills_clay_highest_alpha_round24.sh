#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/YangMills/BalabanP33QuaternionFourFactorTelescopeExact.agda
  DASHI/Physics/YangMills/BalabanP33RationalQuaternionNormSquaredExact.agda
  DASHI/Physics/YangMills/BalabanP33QuaternionTelescopeNormSquaredExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonPlacementTelescopeExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonPlacementNormSquaredExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalLinkJetSelectedFactorNormExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonNamedAtomSumExact.agda
  DASHI/Physics/YangMills/BalabanP33QuaternionAdjointPerturbationExact.agda
  DASHI/Physics/YangMills/BalabanP33QuaternionAdjointNormSquaredExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalBackgroundGaugeFirstExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalBackgroundGaugeDefectNormSquaredExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalBackgroundGaugeGlobalDefectExact.agda
  DASHI/Physics/YangMills/BalabanP33PeriodicDivergenceUpperExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalBackgroundGaugeSignedLowerExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalBackgroundGaugeResidualExact.agda
  DASHI/Physics/YangMills/BalabanP33StrictTerminalGapMarginExact.agda
  DASHI/Physics/YangMills/BalabanP33CoarseFineSchurCouplingExact.agda
  DASHI/Physics/YangMills/BalabanP33EffectiveSchurGapStepExact.agda
  DASHI/Physics/YangMills/BalabanP33StageIStageIISpectralBoundaryExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound24Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

test -f .github/workflows/yang-mills-clay-highest-alpha-round24.yml

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round twenty-four contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

checks=(
  'BalabanP33QuaternionFourFactorTelescopeExact.agda:fourFactorDifferenceTelescopeExact'
  'BalabanP33QuaternionFourFactorTelescopeExact.agda:wilsonScalarDifferenceTelescopeExact'
  'BalabanP33RationalQuaternionNormSquaredExact.agda:normSqMultiplyExact'
  'BalabanP33RationalQuaternionNormSquaredExact.agda:scalarPartSquareBelowNormSq'
  'BalabanP33RationalQuaternionNormSquaredExact.agda:normSqAddBound'
  'BalabanP33RationalQuaternionNormSquaredExact.agda:normSqSum4Bound'
  'BalabanP33QuaternionTelescopeNormSquaredExact.agda:fourTelescopeTermNormSumExact'
  'BalabanP33QuaternionTelescopeNormSquaredExact.agda:fourFactorTelescopeNormSqBound'
  'BalabanP33QuaternionTelescopeNormSquaredExact.agda:wilsonScalarDefectSquareBound'
  'BalabanP33PhysicalWilsonPlacementTelescopeExact.agda:namedPlacementAtomIsSelectedProduct'
  'BalabanP33PhysicalWilsonPlacementTelescopeExact.agda:physicalPlacementAtomsMatchGeneratedProductRule'
  'BalabanP33PhysicalWilsonPlacementTelescopeExact.agda:physicalNamedPlacementDefectTelescopeExact'
  'BalabanP33PhysicalWilsonPlacementTelescopeExact.agda:physicalPlacementWilsonScalarDefectTelescopeExact'
  'BalabanP33PhysicalWilsonPlacementNormSquaredExact.agda:physicalSelectedFactorDefectWeight'
  'BalabanP33PhysicalWilsonPlacementNormSquaredExact.agda:physicalPlacementWilsonScalarDefectSquareBound'
  'BalabanP33PhysicalLinkJetSelectedFactorNormExact.agda:positiveSelectedFactorDefectExact'
  'BalabanP33PhysicalLinkJetSelectedFactorNormExact.agda:inverseSelectedFactorDefectExact'
  'BalabanP33PhysicalLinkJetSelectedFactorNormExact.agda:positiveSelectedFactorNormSqExact'
  'BalabanP33PhysicalLinkJetSelectedFactorNormExact.agda:inverseSelectedFactorNormSqExact'
  'BalabanP33PhysicalWilsonNamedAtomSumExact.agda:physicalPlacementWilsonAtomSumIsPlaquetteVariation'
  'BalabanP33PhysicalWilsonNamedAtomSumExact.agda:physicalPlacementWilsonDefectSumExact'
  'BalabanP33PhysicalWilsonNamedAtomSumExact.agda:physicalNamedWilsonDefectSumIsPhysicalDefect'
  'BalabanP33QuaternionAdjointPerturbationExact.agda:adjointDefectFactorizationExact'
  'BalabanP33QuaternionAdjointPerturbationExact.agda:conjugateDifferenceFromIdentityExact'
  'BalabanP33QuaternionAdjointPerturbationExact.agda:conjugateNormSqExact'
  'BalabanP33QuaternionAdjointPerturbationExact.agda:physicalLinkAdjointDefectFactorizationExact'
  'BalabanP33QuaternionAdjointNormSquaredExact.agda:unitAdjointDefectNormSqBound'
  'BalabanP33QuaternionAdjointNormSquaredExact.agda:physicalLinkAdjointDefectNormSqBound'
  'BalabanP33QuaternionAdjointNormSquaredExact.agda:physicalInverseLinkAdjointDefectNormSqBound'
  'BalabanP33PhysicalBackgroundGaugeFirstExact.agda:backgroundGaugeFirst'
  'BalabanP33PhysicalBackgroundGaugeFirstExact.agda:identityBackgroundGaugeFirstIsPeriodicDivergence'
  'BalabanP33PhysicalBackgroundGaugeFirstExact.agda:axisAdjointDefectFactorizationExact'
  'BalabanP33PhysicalBackgroundGaugeFirstExact.agda:backgroundGaugeFirstMinusFlatExact'
  'BalabanP33PhysicalBackgroundGaugeDefectNormSquaredExact.agda:backgroundGaugeDefectCoordinateIsNegativeSum'
  'BalabanP33PhysicalBackgroundGaugeDefectNormSquaredExact.agda:pointwiseGaugeDefectEnergyBelowQuaternionSum'
  'BalabanP33PhysicalBackgroundGaugeDefectNormSquaredExact.agda:axisAdjointDefectNormSqBound'
  'BalabanP33PhysicalBackgroundGaugeDefectNormSquaredExact.agda:pointwiseGaugeDefectNormSqBound'
  'BalabanP33PhysicalBackgroundGaugeGlobalDefectExact.agda:periodicPhysicalBondNormSqExact'
  'BalabanP33PhysicalBackgroundGaugeGlobalDefectExact.agda:globalGaugeDerivativeDefectBelowLinkCharge'
  'BalabanP33PhysicalBackgroundGaugeGlobalDefectExact.agda:sumPreviousInsertionNormSqExact'
  'BalabanP33PhysicalBackgroundGaugeGlobalDefectExact.agda:globalGaugeDerivativeDefectUniformBound'
  'BalabanP33PeriodicDivergenceUpperExact.agda:backwardDifferenceNormSqBound'
  'BalabanP33PeriodicDivergenceUpperExact.agda:periodicDivergenceUpper'
  'BalabanP33PeriodicDivergenceUpperExact.agda:physicalPeriodicDivergenceUpper'
  'BalabanP33PhysicalBackgroundGaugeSignedLowerExact.agda:weightedGaugeDifferenceLower'
  'BalabanP33PhysicalBackgroundGaugeSignedLowerExact.agda:backgroundGaugeEnergyDifferenceLower'
  'BalabanP33PhysicalBackgroundGaugeSignedLowerExact.agda:backgroundGaugeSignedLowerThirtyTwo'
  'BalabanP33PhysicalBackgroundGaugeSignedLowerExact.agda:backgroundGaugeSignedLowerSixtyFour'
  'BalabanP33PhysicalBackgroundGaugeResidualExact.agda:backgroundGaugeResidualExact'
  'BalabanP33PhysicalBackgroundGaugeResidualExact.agda:backgroundGaugeResidualFirstNormIsEnergy'
  'BalabanP33PhysicalBackgroundGaugeResidualExact.agda:backgroundGaugeResidualSecondVariationIsEnergy'
  'BalabanP33PhysicalBackgroundGaugeResidualExact.agda:backgroundGaugeResidualSignedLowerSixtyFour'
  'BalabanP33StrictTerminalGapMarginExact.agda:marginBudgetAdmissible'
  'BalabanP33StrictTerminalGapMarginExact.agda:admissibleMarginBelowPullback'
  'BalabanP33StrictTerminalGapMarginExact.agda:admissibleMarginBelowFineGap'
  'BalabanP33StrictTerminalGapMarginExact.agda:FourStepPhysicalPositiveMarginBudget'
  'BalabanP33StrictTerminalGapMarginExact.agda:fourStepPhysicalMarginBelowFineGap'
  'BalabanP33CoarseFineSchurCouplingExact.agda:transposeSchurSquared'
  'BalabanP33CoarseFineSchurCouplingExact.agda:schurFeedbackSquaredCoefficient'
  'BalabanP33CoarseFineSchurCouplingExact.agda:coarseFineSchurFeedbackSquared'
  'BalabanP33EffectiveSchurGapStepExact.agda:effectiveSchurLower'
  'BalabanP33EffectiveSchurGapStepExact.agda:SplitRGGapStep'
  'BalabanP33EffectiveSchurGapStepExact.agda:splitStepAsGapTransferStep'
  'BalabanP33EffectiveSchurGapStepExact.agda:splitOneStepPullbackLower'
  'BalabanP33StageIStageIISpectralBoundaryExact.agda:canonicalStageIStageIIBoundary'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

# Primary-source metadata.
grep -q '10.1103/PhysRevD.10.2445' \
  DASHI/Physics/YangMills/BalabanP33QuaternionFourFactorTelescopeExact.agda
grep -q '10.1201/9781439864180' \
  DASHI/Physics/YangMills/BalabanP33RationalQuaternionNormSquaredExact.agda
grep -q '10.1007/978-3-319-13467-3' \
  DASHI/Physics/YangMills/BalabanP33QuaternionAdjointPerturbationExact.agda
grep -q '10.1007/BF01466594' \
  DASHI/Physics/YangMills/BalabanP33PhysicalBackgroundGaugeResidualExact.agda
grep -q '10.1016/S0022-1236(03)00057-0' \
  DASHI/Physics/YangMills/BalabanP33CoarseFineSchurCouplingExact.agda
grep -q '10.1017/fmp.2021.15' \
  DASHI/Physics/YangMills/BalabanP33StageIStageIISpectralBoundaryExact.agda
grep -q '10.1038/nature16059' \
  DASHI/Physics/YangMills/BalabanP33StageIStageIISpectralBoundaryExact.agda
grep -q '10.1017/CBO9781139020411' \
  DASHI/Physics/YangMills/BalabanP33EffectiveSchurGapStepExact.agda
grep -q '10.1007/BF01240221' \
  DASHI/Physics/YangMills/BalabanP33StrictTerminalGapMarginExact.agda

# Scope and hard-math guards.
grep -q 'physicalSelectedBackgroundLinkRadiusLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33PhysicalLinkJetSelectedFactorNormExact.agda
grep -q 'physicalWilsonSignedLocalDefectLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonPlacementNormSquaredExact.agda
grep -q 'physicalSelectedBackgroundInverseLinkRadiusLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33PhysicalBackgroundGaugeGlobalDefectExact.agda
grep -q 'physicalConfiguredInverseLinkRadiusProducerLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33PhysicalBackgroundGaugeSignedLowerExact.agda
grep -q 'physicalCoarseFineCouplingBoundsLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33CoarseFineSchurCouplingExact.agda
grep -q 'physicalEffectiveActionSecondDerivativeLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33EffectiveSchurGapStepExact.agda
grep -q 'physicalStrictLossBudgetProducerLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33StrictTerminalGapMarginExact.agda
grep -q 'margin + Fixed.fourStepWeightedLoss' \
  DASHI/Physics/YangMills/BalabanP33StrictTerminalGapMarginExact.agda
grep -q 'couplingLoss + remainderLoss' \
  DASHI/Physics/YangMills/BalabanP33EffectiveSchurGapStepExact.agda
grep -q 'undecidability theorem is not imported as an Agda proof' \
  DASHI/Physics/YangMills/BalabanP33CoarseFineSchurCouplingExact.agda
grep -q 'finiteCoercivityAutomaticallyGivesThermodynamicGapIsFalse' \
  DASHI/Physics/YangMills/BalabanP33StageIStageIISpectralBoundaryExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound24Validation.agda
