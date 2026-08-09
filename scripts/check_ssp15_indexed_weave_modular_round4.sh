#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_ssp15_j_coarse_fine_round3.sh

sources=(
  DASHI/Core/IndexedWeaveHyperfabricExact.agda
  DASHI/Biology/SSPIndexedWeaveHyperfabricExact.agda
  DASHI/Biology/ModularCoarseFineAddressFibrationExact.agda
  DASHI/Biology/SSPIndexedWeaveModularIntegrationExact.agda
  DASHI/Biology/LayeredBindingSystemExact.agda
  DASHI/Computation/JacquardOperationalSemanticsExact.agda
  DASHI/Topology/HelicalWeaveMappingTorusExact.agda
  DASHI/Reasoning/DistributedBraidGluingExact.agda
  DASHI/Dynamics/KAMHypothesisCoreExact.agda
  DASHI/Physics/Moonshine/MoonshineTraceIndexedWeaveExact.agda
  DASHI/Physics/Closure/KleinQuarticGenerationSymmetryExact.agda
  DASHI/Biology/SSP15IndexedWeaveModularRound4Validation.agda
  DASHI/EverythingSSP15IndexedWeaveModularRound4.agda
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
modular=DASHI/Biology/ModularCoarseFineAddressFibrationExact.agda
integrated=DASHI/Biology/SSPIndexedWeaveModularIntegrationExact.agda
binding=DASHI/Biology/LayeredBindingSystemExact.agda
jacquard=DASHI/Computation/JacquardOperationalSemanticsExact.agda
helix=DASHI/Topology/HelicalWeaveMappingTorusExact.agda
distributed=DASHI/Reasoning/DistributedBraidGluingExact.agda
kam=DASHI/Dynamics/KAMHypothesisCoreExact.agda
moonshine=DASHI/Physics/Moonshine/MoonshineTraceIndexedWeaveExact.agda
klein=DASHI/Physics/Closure/KleinQuarticGenerationSymmetryExact.agda
validation=DASHI/Biology/SSP15IndexedWeaveModularRound4Validation.agda
top=DASHI/EverythingSSP15IndexedWeaveModularRound4.agda

require_pattern "$indexed" 'record IndexedWeave'
require_pattern "$indexed" 'transportComp'
require_pattern "$indexed" 'Residual : Index → Set'
require_pattern "$ssp" 'canonicalSSPIndexedWeave'
require_pattern "$ssp" 'reverseTwicePreservesEveryLaneState'
require_pattern "$ssp" 'reversePathRetainsTargetResidual'
require_pattern "$modular" 'jCoarseAddressDepth = 1'
require_pattern "$modular" 'jFineAddressDepth = 10'
require_pattern "$modular" 'jAbsoluteAddressDepth = 11'
require_pattern "$modular" 'jAbsoluteStateCountFactors'
require_pattern "$modular" 'FineAddress = FineSector → Harmonic.BalancedTrit'
require_pattern "$modular" 'frickeComplementPointwiseInvolutive'
require_pattern "$integrated" 'canonicalSSPModularIndexedWeave'
require_pattern "$integrated" 'integratedPathsPreserveCoarseBase'
require_pattern "$integrated" 'fineAddressSurvivesLaneTransport'
require_pattern "$binding" 'coarseProjectionIsNotInjective'
require_pattern "$binding" 'bindingCanBePresentWhileDepthContinuityFails'
require_pattern "$binding" 'boundaryDefectRepeatsAcrossSuperplies'
require_pattern "$jacquard" 'compilePreservesExecution'
require_pattern "$jacquard" 'compiledCrossingWordAgrees'
require_pattern "$helix" 'rotationHasOrderThree'
require_pattern "$helix" 'threeStepsReturnToSamePhase'
require_pattern "$distributed" 'singleOwnerNonInjective'
require_pattern "$distributed" 'rotationObservationEquivariant'
require_pattern "$kam" '10.1002/cpa.3160350504'
require_pattern "$kam" 'orderThreeRotationRefutesNoReturn'
require_pattern "$moonshine" 'traceProjectionIsNonInjective'
require_pattern "$moonshine" 'canonicalMoonshineTraceIndexedWeave'
require_pattern "$klein" 'noFullySymmetricSelectedFactor'
require_pattern "$klein" 'receiptStillBlocksPhysicalCKMPromotion'
require_pattern "$validation" 'import DASHI.Biology.SSPIndexedWeaveModularIntegrationExact'
require_pattern "$top" 'import DASHI.EverythingSSP15JCoarseFineRound3'

python3 -m py_compile scripts/classify_agda_substance.py
python3 scripts/classify_agda_substance.py --self-test
mkdir -p artifacts
python3 scripts/classify_agda_substance.py \
  --fail-on-external \
  --output artifacts/ssp15-indexed-weave-substance.json \
  "${sources[@]}"

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/SSP15IndexedWeaveModularRound4Validation.agda \
  DASHI/EverythingSSP15IndexedWeaveModularRound4.agda
