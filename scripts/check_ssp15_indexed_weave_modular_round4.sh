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
  DASHI/Reasoning/AttractorAlignedBranchSelectionExact.agda
  DASHI/Reasoning/ChildhoodReligiousCoercionExact.agda
  DASHI/Reasoning/TraumaAttractorBranchRegulationExact.agda
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
  test -s "$source" || { echo "missing or empty source $source" >&2; exit 1; }
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
  test -s "$source" || { echo "missing legacy surface $source" >&2; exit 1; }
done

require_pattern() {
  local source="$1"
  local pattern="$2"
  grep -F "$pattern" "$source" >/dev/null || {
    echo "missing required marker '$pattern' in $source" >&2
    exit 1
  }
}

require_pattern DASHI/Core/IndexedWeaveHyperfabricExact.agda 'record IndexedWeave'
require_pattern DASHI/Biology/SSPIndexedWeaveHyperfabricExact.agda 'composeOrientationAssoc'
require_pattern DASHI/Biology/SSPHyperfibreLawfulUpgradeExact.agda 'legacyTransportAgrees'
require_pattern DASHI/Biology/ModularCoarseFineAddressFibrationExact.agda 'canonicalFineAddressTenCoordinateEquivalence'
require_pattern DASHI/Biology/ModularCoarseFineAddressFibrationExact.agda 'finiteHauptmodulFrickeInvariant'
require_pattern DASHI/Biology/SSPIndexedWeaveModularIntegrationExact.agda 'canonicalSSPModularIndexedWeave'
require_pattern DASHI/Biology/LayeredBindingSystemExact.agda 'coarseProjectionIsNotInjective'
require_pattern DASHI/Computation/JacquardOperationalSemanticsExact.agda 'compilePreservesExecution'
require_pattern DASHI/Computation/JacquardHelicalWeaveBridgeExact.agda 'phase0Warp2CrossingWord'
require_pattern DASHI/Topology/HelicalWeaveMappingTorusExact.agda 'rotationHasOrderThree'
require_pattern DASHI/Reasoning/DistributedBraidGluingExact.agda 'singleOwnerNonInjective'
require_pattern DASHI/Unified/ThreePhaseCrossPollinationExact.agda 'sharedC3ShapeImpliesPhysicalIdentityIsFalse'
require_pattern DASHI/Dynamics/KAMHypothesisCoreExact.agda 'KAMAuthority'
require_pattern DASHI/Physics/Moonshine/MoonshineTraceIndexedWeaveExact.agda 'identityTransportRetainsHiddenTraceResidual'
require_pattern DASHI/Physics/Moonshine/SSPMoonshineTraceFibreIntegrationExact.agda 'sameObservedTraceRemainsHiddenDistinctInEveryLane'
require_pattern DASHI/Physics/Closure/KleinQuarticGenerationSymmetryExact.agda 'noFullySymmetricSelectedFactor'

branch=DASHI/Reasoning/AttractorAlignedBranchSelectionExact.agda
coercion=DASHI/Reasoning/ChildhoodReligiousCoercionExact.agda
trauma=DASHI/Reasoning/TraumaAttractorBranchRegulationExact.agda
validation=DASHI/Biology/SSP15IndexedWeaveModularRound4Validation.agda

require_pattern "$branch" 'moreOptionsCanWorsenReachableStructure'
require_pattern "$branch" 'duplicateOptionsCanShareOneBlockedBasin'
require_pattern "$branch" 'explorationCanBeRetainedWithoutPositiveDrift'
require_pattern "$branch" 'feasibleLookingBranchCanInterfereWithDirectRoute'
require_pattern "$coercion" 'complianceProjectionIsNonInjective'
require_pattern "$coercion" 'silenceIsNotAssent'
require_pattern "$coercion" 'restrictedRefusalAndPenaltyConstructCoercion'
require_pattern "$coercion" 'religiousContentAloneDoesNotConstructCoercion'
require_pattern "$coercion" 'retaliationConstructsInstitutionalBetrayal'
require_pattern "$trauma" 'regulationOverridesHoardingForTrapBranch'
require_pattern "$trauma" 'regulationOverridesPrematureClosureForExploration'
require_pattern "$trauma" 'healthyRegulationIsContextSensitive'
require_pattern "$validation" 'import DASHI.Reasoning.AttractorAlignedBranchSelectionExact'
require_pattern "$validation" 'import DASHI.Reasoning.ChildhoodReligiousCoercionExact'
require_pattern "$validation" 'import DASHI.Reasoning.TraumaAttractorBranchRegulationExact'

python3 -m py_compile scripts/classify_agda_substance.py
python3 scripts/classify_agda_substance.py --self-test
mkdir -p artifacts
python3 scripts/classify_agda_substance.py \
  --fail-on-external \
  --output artifacts/ssp15-indexed-weave-substance.json \
  "${sources[@]}"
python3 scripts/classify_agda_substance.py \
  --output artifacts/cross-pollination-substance.json \
  "${legacy_surfaces[@]}"

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/SSP15IndexedWeaveModularRound4Validation.agda \
  DASHI/EverythingSSP15IndexedWeaveModularRound4.agda
