#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/YangMills/BalabanP33QuaternionFourFactorTelescopeExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonPlacementTelescopeExact.agda
  DASHI/Physics/YangMills/BalabanP33QuaternionAdjointPerturbationExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalBackgroundGaugeFirstExact.agda
  DASHI/Physics/YangMills/BalabanP33StrictTerminalGapMarginExact.agda
  DASHI/Physics/YangMills/BalabanP33CoarseFineSchurCouplingExact.agda
  DASHI/Physics/YangMills/BalabanP33EffectiveSchurGapStepExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound24Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round twenty-four contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

checks=(
  'BalabanP33QuaternionFourFactorTelescopeExact.agda:fourFactorDifferenceTelescopeExact'
  'BalabanP33QuaternionFourFactorTelescopeExact.agda:wilsonScalarDifferenceTelescopeExact'
  'BalabanP33PhysicalWilsonPlacementTelescopeExact.agda:namedPlacementAtomIsSelectedProduct'
  'BalabanP33PhysicalWilsonPlacementTelescopeExact.agda:physicalPlacementAtomsMatchGeneratedProductRule'
  'BalabanP33PhysicalWilsonPlacementTelescopeExact.agda:physicalNamedPlacementDefectTelescopeExact'
  'BalabanP33PhysicalWilsonPlacementTelescopeExact.agda:physicalPlacementWilsonScalarDefectTelescopeExact'
  'BalabanP33QuaternionAdjointPerturbationExact.agda:adjointDefectFactorizationExact'
  'BalabanP33QuaternionAdjointPerturbationExact.agda:conjugateDifferenceFromIdentityExact'
  'BalabanP33QuaternionAdjointPerturbationExact.agda:conjugateNormSqExact'
  'BalabanP33QuaternionAdjointPerturbationExact.agda:physicalLinkAdjointDefectFactorizationExact'
  'BalabanP33PhysicalBackgroundGaugeFirstExact.agda:backgroundGaugeFirst'
  'BalabanP33PhysicalBackgroundGaugeFirstExact.agda:identityBackgroundGaugeFirstIsPeriodicDivergence'
  'BalabanP33PhysicalBackgroundGaugeFirstExact.agda:axisAdjointDefectFactorizationExact'
  'BalabanP33PhysicalBackgroundGaugeFirstExact.agda:backgroundGaugeFirstMinusFlatExact'
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
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

# Primary-source metadata.
grep -q '10.1103/PhysRevD.10.2445' \
  DASHI/Physics/YangMills/BalabanP33QuaternionFourFactorTelescopeExact.agda
grep -q '10.1007/978-3-319-13467-3' \
  DASHI/Physics/YangMills/BalabanP33QuaternionAdjointPerturbationExact.agda
grep -q '10.1007/BF01466594' \
  DASHI/Physics/YangMills/BalabanP33PhysicalBackgroundGaugeFirstExact.agda
grep -q '10.1016/S0022-1236(03)00057-0' \
  DASHI/Physics/YangMills/BalabanP33CoarseFineSchurCouplingExact.agda
grep -q '10.1017/fmp.2021.15' \
  DASHI/Physics/YangMills/BalabanP33CoarseFineSchurCouplingExact.agda
grep -q '10.1038/nature16059' \
  DASHI/Physics/YangMills/BalabanP33CoarseFineSchurCouplingExact.agda
grep -q '10.1017/CBO9781139020411' \
  DASHI/Physics/YangMills/BalabanP33EffectiveSchurGapStepExact.agda
grep -q '10.1007/BF01240221' \
  DASHI/Physics/YangMills/BalabanP33StrictTerminalGapMarginExact.agda

# Scope and hard-math guards.
grep -q 'physicalWilsonPlacementNormEstimateLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonPlacementTelescopeExact.agda
grep -q 'physicalBackgroundGaugeDefectNormLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33PhysicalBackgroundGaugeFirstExact.agda
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
grep -q 'No physical RG estimate is asserted here' \
  DASHI/Physics/YangMills/BalabanP33EffectiveSchurGapStepExact.agda
grep -q 'undecidability theorem is not imported as an Agda proof' \
  DASHI/Physics/YangMills/BalabanP33CoarseFineSchurCouplingExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound24Validation.agda
