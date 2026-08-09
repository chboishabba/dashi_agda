#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_ssp15_j_coarse_fine_round3.sh

sources=(
  DASHI/Core/IndexedWeaveHyperfabricExact.agda
  DASHI/Biology/SSPIndexedWeaveHyperfabricExact.agda
  DASHI/Biology/SSPHyperfibreLawfulUpgradeExact.agda
  DASHI/Biology/ModularCoarseFineAddressFibrationExact.agda
  DASHI/Biology/SSPIndexedWeaveModularIntegrationExact.agda
  DASHI/Biology/LayeredBindingSystemExact.agda
  DASHI/Computation/JacquardOperationalSemanticsExact.agda
  DASHI/Computation/JacquardHelicalWeaveBridgeExact.agda
  DASHI/Topology/HelicalWeaveMappingTorusExact.agda
  DASHI/Reasoning/DistributedBraidGluingExact.agda
  DASHI/Unified/ThreePhaseCrossPollinationExact.agda
  DASHI/Dynamics/KAMHypothesisCoreExact.agda
  DASHI/Physics/Moonshine/MoonshineTraceIndexedWeaveExact.agda
  DASHI/Physics/Moonshine/SSPMoonshineTraceFibreIntegrationExact.agda
  DASHI/Physics/Closure/KleinQuarticGenerationSymmetryExact.agda
  DASHI/Biology/SSP15IndexedWeaveModularRound4Validation.agda
  DASHI/EverythingSSP15IndexedWeaveModularRound4.agda
)

legacy_surfaces=(
  DASHI/Core/LoomEncoding.agda
  DASHI/Physics/Moonshine/MoonshineCategoricalLoom.agda
  DASHI/Physics/Closure/KleinQuarticQMReceipt.agda
  DASHI/Physics/Closure/DHRIntertwinerPSL2F7TextureReceipt.agda
  DASHI/Physics/Closure/CKMV3SpurionTextureFrontierReceipt.agda
  DASHI/Physics/Closure/YukawaDHRIntertwinerCompatibility.agda
  DASHI/Physics/Closure/CrossGateCompositionTheorems.agda
  DASHI/Biology/SSPHyperfibreSymmetryTowerExact.agda
  DASHI/Biology/SelfIndexingHyperfabricTetrationExact.agda
  DASHI/Biology/SignedSSPFRACTRANWeaveExact.agda
)

for source in "${sources[@]}"; do
  if [ ! -s "$source" ]; then
    echo "missing or empty source $source" >&2
    exit 1
  fi
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|--allow-unsolved-metas|--no-termination-check|--no-positivity-check|--type-in-type|--omega-in-omega|--rewriting|--unsafe|TERMINATING|NON_COVERING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|trustMe|primTrustMe|(^|[[:space:]])\?([[:space:];)]|$)' "$source"; then
    echo "forbidden trust escape or hole in $source" >&2
    exit 1
  fi
  if grep -Pzo '\{!.*?!\}' "$source" >/dev/null; then
    echo "forbidden interaction hole in $source" >&2
    exit 1
  fi
done

for source in "${legacy_surfaces[@]}"; do
  if [ ! -s "$source" ]; then
    echo "missing legacy cross-pollination surface $source" >&2
    exit 1
  fi
done

require_pattern() {
  local source="$1"
  local pattern="$2"
  if ! grep -F "$pattern" "$source" >/dev/null; then
    echo "missing required marker '$pattern' in $source" >&2
    exit 1
  fi
}

indexed=DASHI/Core/IndexedWeaveHyperfabricExact.agda
ssp=DASHI/Biology/SSPIndexedWeaveHyperfabricExact.agda
upgrade=DASHI/Biology/SSPHyperfibreLawfulUpgradeExact.agda
modular=DASHI/Biology/ModularCoarseFineAddressFibrationExact.agda
integrated=DASHI/Biology/SSPIndexedWeaveModularIntegrationExact.agda
binding=DASHI/Biology/LayeredBindingSystemExact.agda
jacquard=DASHI/Computation/JacquardOperationalSemanticsExact.agda
jacquard_helix=DASHI/Computation/JacquardHelicalWeaveBridgeExact.agda
helix=DASHI/Topology/HelicalWeaveMappingTorusExact.agda
distributed=DASHI/Reasoning/DistributedBraidGluingExact.agda
three_phase=DASHI/Unified/ThreePhaseCrossPollinationExact.agda
kam=DASHI/Dynamics/KAMHypothesisCoreExact.agda
moonshine=DASHI/Physics/Moonshine/MoonshineTraceIndexedWeaveExact.agda
ssp_moonshine=DASHI/Physics/Moonshine/SSPMoonshineTraceFibreIntegrationExact.agda
klein=DASHI/Physics/Closure/KleinQuarticGenerationSymmetryExact.agda
validation=DASHI/Biology/SSP15IndexedWeaveModularRound4Validation.agda
top=DASHI/EverythingSSP15IndexedWeaveModularRound4.agda

require_pattern "$indexed" 'record IndexedWeave'
require_pattern "$indexed" 'transportComp'
require_pattern "$indexed" 'Residual : Index → Set'
require_pattern "$indexed" 'stateResidual'
require_pattern "$ssp" 'composeOrientationAssoc'
require_pattern "$ssp" 'canonicalSSPIndexedWeave'
require_pattern "$ssp" 'inverseTwicePreservesEveryLaneState'
require_pattern "$ssp" 'inverseTwiceComposesToForward'
require_pattern "$ssp" 'inversePathRetainsTargetResidual'
require_pattern "$upgrade" 'legacyTransportAgrees'
require_pattern "$upgrade" 'legacyResidualAgrees'
require_pattern "$upgrade" 'canonicalSSPHyperfibreLawfulUpgrade'
require_pattern "$modular" 'jCoarseAddressDepth = 1'
require_pattern "$modular" 'jFineAddressDepth = 10'
require_pattern "$modular" 'jAbsoluteAddressDepth = 11'
require_pattern "$modular" 'jAbsoluteStateCountFactors'
require_pattern "$modular" 'FineAddress = FineSector → Harmonic.BalancedTrit'
require_pattern "$modular" 'canonicalFineAddressTenCoordinateEquivalence'
require_pattern "$modular" 'finiteHauptmodulFrickeInvariant'
require_pattern "$modular" 'counterLiftIsFrickeOfDirectLift'
require_pattern "$modular" 'finiteFrickePullbackPointwiseInvolutive'
require_pattern "$integrated" 'canonicalSSPModularIndexedWeave'
require_pattern "$integrated" 'integratedPathsPreserveCoarseBase'
require_pattern "$integrated" 'fineAddressSurvivesLaneTransport'
require_pattern "$integrated" 'inverseIntegratedPathRetainsInverseResidual'
require_pattern "$binding" 'coarseProjectionIsNotInjective'
require_pattern "$binding" 'bindingCanBePresentWhileDepthContinuityFails'
require_pattern "$binding" 'boundaryDefectRepeatsAcrossSuperplies'
require_pattern "$jacquard" 'compilePreservesExecution'
require_pattern "$jacquard" 'compiledCrossingWordAgrees'
require_pattern "$jacquard_helix" 'compileHelicalProgram'
require_pattern "$jacquard_helix" 'phase0Warp2CrossingWord'
require_pattern "$helix" 'rotationHasOrderThree'
require_pattern "$helix" 'threeStepsReturnToSamePhase'
require_pattern "$distributed" 'singleOwnerNonInjective'
require_pattern "$distributed" 'rotationObservationEquivariant'
require_pattern "$three_phase" 'phaseAgentRotationEquivariant'
require_pattern "$three_phase" 'phaseFactorRotationEquivariant'
require_pattern "$three_phase" 'factorSlotC3'
require_pattern "$three_phase" 'sharedC3ShapeImpliesPhysicalIdentityIsFalse'
require_pattern "$kam" '10.1002/cpa.3160350504'
require_pattern "$kam" 'orderThreeRotationRefutesNoReturn'
require_pattern "$kam" 'KAMAuthority'
require_pattern "$moonshine" 'traceProjectionIsNonInjective'
require_pattern "$moonshine" 'canonicalMoonshineTraceIndexedWeave'
require_pattern "$moonshine" 'identityTransportRetainsHiddenTraceResidual'
require_pattern "$ssp_moonshine" 'canonicalSSPMoonshineTraceIndexedWeave'
require_pattern "$ssp_moonshine" 'sameObservedTraceRemainsHiddenDistinctInEveryLane'
require_pattern "$ssp_moonshine" 'inverseLaneTransportRetainsHiddenTraceTag'
require_pattern "$ssp_moonshine" 'MonsterSuppliesCanonicalCrossLaneCompatibilityIsFalse'
require_pattern "$klein" 'noFullySymmetricSelectedFactor'
require_pattern "$klein" 'receiptStillBlocksPhysicalCKMPromotion'
require_pattern "$validation" 'import DASHI.Biology.SSPHyperfibreLawfulUpgradeExact'
require_pattern "$validation" 'import DASHI.Biology.SSPIndexedWeaveModularIntegrationExact'
require_pattern "$validation" 'import DASHI.Computation.JacquardHelicalWeaveBridgeExact'
require_pattern "$validation" 'import DASHI.Unified.ThreePhaseCrossPollinationExact'
require_pattern "$validation" 'import DASHI.Physics.Moonshine.SSPMoonshineTraceFibreIntegrationExact'
require_pattern "$top" 'import DASHI.EverythingSSP15JCoarseFineRound3'

python3 -m py_compile scripts/classify_agda_substance.py
python3 scripts/classify_agda_substance.py --self-test
mkdir -p artifacts
python3 scripts/classify_agda_substance.py \
  --fail-on-external \
  --output artifacts/ssp15-indexed-weave-substance.json \
  "${sources[@]}"

# This second report is deliberately informational: legacy surfaces may expose
# postulated or governance-only structure, and the point is to measure rather
# than conceal that implementation shape.
python3 scripts/classify_agda_substance.py \
  --output artifacts/cross-pollination-substance.json \
  "${legacy_surfaces[@]}"

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/SSP15IndexedWeaveModularRound4Validation.agda \
  DASHI/EverythingSSP15IndexedWeaveModularRound4.agda
