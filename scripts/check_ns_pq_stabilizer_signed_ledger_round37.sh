#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

# Round 37 is cumulative: fail immediately if the repaired Round-36 tranche is
# no longer structurally valid.
bash scripts/check_ns_schur_principal_angle_projective_round36.sh

files=(
  DASHI/Physics/Closure/NSTriadKNComPQCrossChannelRound37Exact.agda
  DASHI/Physics/Closure/NSTriadKNComPQInvolutionRound37Exact.agda
  DASHI/Physics/Closure/NSTriadKNDirectionalProjectorStabilizerRound37Exact.agda
  DASHI/Physics/Closure/NSTriadKNDirectionalProjectorDefectBridgeRound37Exact.agda
  DASHI/Physics/Closure/NSTriadKNFinitePVProjectorIncrementRound37Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHBadScaleInvariantGeometryObstructionRound37Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHBadEnergyNormalizedCoercivityRound37Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHBadCrossingVariationCostRound37Exact.agda
  DASHI/Physics/Closure/NSTriadKNSignedOwnerPreledgerRound37Exact.agda
  DASHI/Physics/Closure/NSTriadKNScopedClassificationWitnessRound37Exact.agda
  DASHI/Physics/Closure/NSTriadKNShellBudgetProjectiveTelescopeRound37Exact.agda
  DASHI/Physics/Closure/NSTriadKNShellLedgerInverseSystemRound37Exact.agda
  DASHI/Physics/Closure/NSTriadKNCertifiedOwnerReserveOptimizationRound37Exact.agda
  DASHI/Physics/Closure/NSTriadKNRationalPhysicalTriadEnergyRound37Exact.agda
  DASHI/Physics/Closure/NSTriadKNPQStabilizerSignedLedgerRound37Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
  if grep -En '(^|[[:space:]])(postulate|primitive)[[:space:]]|\{!!\}|\?|trustMe|unsafe|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|funext|Properties\.WithK|unique⇒irrelevant|--with-K' "$file"; then
    echo "forbidden proof escape in $file" >&2
    exit 1
  fi
done

# Concrete theorem markers.  These are deliberately mathematical statements,
# not status-only receipts.
grep -q 'commutatorIsCrossChannelDifference' DASHI/Physics/Closure/NSTriadKNComPQCrossChannelRound37Exact.agda
grep -q 'commutatorNormSquaredCrossChannelExact' DASHI/Physics/Closure/NSTriadKNComPQCrossChannelRound37Exact.agda
grep -q 'involutionConjugatesCoarseToFine' DASHI/Physics/Closure/NSTriadKNComPQInvolutionRound37Exact.agda
grep -q 'projectorDefectIncrementFactorization' DASHI/Physics/Closure/NSTriadKNDirectionalProjectorStabilizerRound37Exact.agda
grep -q 'rankOneProjectorNegationInvariant' DASHI/Physics/Closure/NSTriadKNDirectionalProjectorStabilizerRound37Exact.agda
grep -q 'projectorDefectIsTwiceExistingDirectionalDefect' DASHI/Physics/Closure/NSTriadKNDirectionalProjectorDefectBridgeRound37Exact.agda
grep -q 'finitePVProjectorIncrementIdentity' DASHI/Physics/Closure/NSTriadKNFinitePVProjectorIncrementRound37Exact.agda
grep -q 'uniformDirectionOnlyFloorMustBeNonpositive' DASHI/Physics/Closure/NSTriadKNHHBadScaleInvariantGeometryObstructionRound37Exact.agda
grep -q 'badEnergyCoercivityProducesInverseShellCharging' DASHI/Physics/Closure/NSTriadKNHHBadEnergyNormalizedCoercivityRound37Exact.agda
grep -q 'hystereticCrossingCostBound' DASHI/Physics/Closure/NSTriadKNHHBadCrossingVariationCostRound37Exact.agda
grep -q 'internalTransferPreservesPairNet' DASHI/Physics/Closure/NSTriadKNSignedOwnerPreledgerRound37Exact.agda
grep -q 'mapClassification' DASHI/Physics/Closure/NSTriadKNScopedClassificationWitnessRound37Exact.agda
grep -q 'internalAdvanceTelescope' DASHI/Physics/Closure/NSTriadKNShellBudgetProjectiveTelescopeRound37Exact.agda
grep -q 'coarsenCanonicalSuccessor' DASHI/Physics/Closure/NSTriadKNShellLedgerInverseSystemRound37Exact.agda
grep -q 'certifiedMinimizerMaximizesReserve' DASHI/Physics/Closure/NSTriadKNCertifiedOwnerReserveOptimizationRound37Exact.agda
grep -q 'literalCutoffTriadPowerSumZero' DASHI/Physics/Closure/NSTriadKNRationalPhysicalTriadEnergyRound37Exact.agda

# Provenance checks for the load-bearing external inputs.
grep -q '10.1002/cpa.3160410704' DASHI/Physics/Closure/NSTriadKNComPQCrossChannelRound37Exact.agda
grep -q '10.1512/iumj.1993.42.42034' DASHI/Physics/Closure/NSTriadKNDirectionalProjectorStabilizerRound37Exact.agda
grep -q '10.1007/s00021-019-0411-z' DASHI/Physics/Closure/NSTriadKNHHBadEnergyNormalizedCoercivityRound37Exact.agda
grep -q '10.1007/BF02547354' DASHI/Physics/Closure/NSTriadKNRationalPhysicalTriadEnergyRound37Exact.agda

# The physical frontier must remain fail-closed.
grep -q 'physicalComCrossChannelOperatorRealizationConstructed = false' DASHI/Physics/Closure/NSTriadKNComPQCrossChannelRound37Exact.agda
grep -q 'periodicPVProjectorDefectEstimateConstructed = false' DASHI/Physics/Closure/NSTriadKNDirectionalProjectorStabilizerRound37Exact.agda
grep -q 'literalPeriodicStrainKernelZeroMassConstructed = false' DASHI/Physics/Closure/NSTriadKNFinitePVProjectorIncrementRound37Exact.agda
grep -q 'physicalHHBadEnergyCoercivityConstructed = false' DASHI/Physics/Closure/NSTriadKNHHBadEnergyNormalizedCoercivityRound37Exact.agda
grep -q 'physicalPositiveVariationBoundConstructed = false' DASHI/Physics/Closure/NSTriadKNHHBadCrossingVariationCostRound37Exact.agda
grep -q 'analyticOwnerLedgerInverseLimitConstructed = false' DASHI/Physics/Closure/NSTriadKNShellLedgerInverseSystemRound37Exact.agda
grep -q 'literalGalerkinPowerEqualsEnumeratedTriadFoldConstructed = false' DASHI/Physics/Closure/NSTriadKNRationalPhysicalTriadEnergyRound37Exact.agda

chmod +x scripts/agda29_without_k_wrapper.sh
AGDA_BIN="$root/scripts/agda29_without_k_wrapper.sh" \
  scripts/run_agda29_parallel_check.sh \
  DASHI.Physics.Closure.NSTriadKNPQStabilizerSignedLedgerRound37Validation

echo "Round37 P/Q-stabilizer-signed-ledger checks passed"
