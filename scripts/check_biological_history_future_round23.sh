#!/usr/bin/env bash
# Source/finite regressions followed by repository-owned parallel Agda checker.
set -euo pipefail
cd "$(dirname "$0")/.."

ROOT=DASHI/EverythingBiologicalHistoryFutureRound23.agda
MODULES=(
  DASHI/Biology/Physical/BiologicalHistoryFutureQuotientExact.agda
  DASHI/Biology/Physical/BiologicalEvidenceFeedbackFiniteExact.agda
  DASHI/Biology/Physical/SourceIndexedBiologicalCarrierExact.agda
  DASHI/Biology/Physical/BiologicalFuturePartitionCompilerExact.agda
  DASHI/Biology/Physical/BiologicalStochasticFutureLumpingExact.agda
  DASHI/Biology/Physical/BiologicalParametricStochasticLumpingExact.agda
  DASHI/Biology/Physical/BiologicalCoupledTissueCubeExact.agda
  DASHI/Biology/Physical/BiologicalMinimalMorphologyFutureQuotientExact.agda
  DASHI/Biology/Physical/BiologicalMinimalMorphologyAdversarialRefinementExact.agda
  DASHI/Biology/Physical/BiologicalMorphologyPartitionDepth4Exact.agda
  DASHI/Biology/Physical/BiologicalFullCubeIncidenceExact.agda
  DASHI/Biology/Physical/BiologicalAllNeighbourTissueDynamicsExact.agda
  DASHI/Biology/Physical/OriginalDmscTwoGenotypeMeasuredExact.agda
  DASHI/Biology/Physical/BiologicalRNA9HammingExact.agda
  DASHI/Biology/Physical/Biological369CubicalOpenSignedChargeExact.agda
  DASHI/Biology/Physical/Biological369CubicalBoundaryMaterialExact.agda
  DASHI/Biology/Physical/Biological369OriginalThreeWayPantsFluxExact.agda
  DASHI/Biology/Physical/Biological369PantsPhysicalSeamExact.agda
  DASHI/Biology/Physical/Biological369CubicalMaterialFieldExact.agda
  DASHI/Biology/Physical/BiologicalSignedIonicSharedGridExact.agda
  DASHI/Biology/Physical/BiologicalOriginal54BondSharedVectorExact.agda
  DASHI/Biology/Physical/BiologicalSharedFiniteVectorTransferExact.agda
  DASHI/Biology/Physical/BiologicalSharedFiniteChainConservationExact.agda
  DASHI/Biology/Physical/BiologicalSharedChainFiniteVolumeExact.agda
  DASHI/Biology/Physical/BiologicalSpatialCirculationIncidenceExact.agda
  DASHI/Biology/Physical/BiologicalSourcePhysicalTissueSimulationExact.agda
  DASHI/Biology/Physical/BiologicalElectrodiffusionTissueDonorExact.agda
  DASHI/Biology/Physical/BiologicalAtomicMolecularHammingReuseExact.agda
)
test -s "$ROOT"
for module in "${MODULES[@]}"; do
  test -s "$module"
  if grep -vE '^[[:space:]]*--' "$module" \
       | grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!!\}|--allow-unsolved-metas|primTrustMe'; then
    echo "Unsafe proof escape in $module" >&2
    exit 1
  fi
  grep -q "^module " "$module"
done

grep -q 'compiledCodeExactlyCapturesFutureLanguage' \
  DASHI/Biology/Physical/BiologicalFuturePartitionCompilerExact.agda
grep -q 'allStochasticHorizonsRemainCoarse' \
  DASHI/Biology/Physical/BiologicalStochasticFutureLumpingExact.agda
grep -q 'allStochasticHorizonsPreserveMinimal18Classes' DASHI/Biology/Physical/BiologicalParametricStochasticLumpingExact.agda
grep -q 'timeVaryingStochasticHistoriesPreserveMinimal18Classes' DASHI/Biology/Physical/BiologicalParametricStochasticLumpingExact.agda
grep -q 'parametricAllFiniteHorizonsRemainCoarse' DASHI/Biology/Physical/BiologicalParametricStochasticLumpingExact.agda
grep -q 'arbitraryNormalizedWeightsPreserveAllControlledFutures' DASHI/Biology/Physical/BiologicalParametricStochasticLumpingExact.agda
grep -q 'allControlledStochasticHistoriesRemainCoarse' \
  DASHI/Biology/Physical/BiologicalStochasticFutureLumpingExact.agda
grep -q 'initialAllTracesPreserveBiologicalProjection' \
  DASHI/Biology/Physical/BiologicalCoupledTissueCubeExact.agda
grep -q 'coupledSignalIdempotentAt' \
  DASHI/Biology/Physical/BiologicalCoupledTissueCubeExact.agda
grep -q 'original18ClassProjectionNotSafeUnderNewDynamics' DASHI/Biology/Physical/BiologicalMinimalMorphologyAdversarialRefinementExact.agda
grep -q 'morphologyFutureEquivalenceExactlyMinimalCode' \
  DASHI/Biology/Physical/BiologicalMinimalMorphologyFutureQuotientExact.agda
grep -q 'morphologyCompilerStopsAtFour' \
  DASHI/Biology/Physical/BiologicalMorphologyPartitionDepth4Exact.agda
grep -q 'completePlaquetteCount' \
  DASHI/Biology/Physical/BiologicalFullCubeIncidenceExact.agda
grep -q 'canonicalAllNeighboursFutureSafe' \
  DASHI/Biology/Physical/BiologicalAllNeighbourTissueDynamicsExact.agda
grep -q 'differentRawMeanReadouts' \
  DASHI/Biology/Physical/OriginalDmscTwoGenotypeMeasuredExact.agda
grep -q 'physicalHistoryProjectsToAll54Bonds' DASHI/Biology/Physical/BiologicalSourcePhysicalTissueSimulationExact.agda
grep -q 'sourcePoissonChargeAgrees' DASHI/Biology/Physical/BiologicalElectrodiffusionTissueDonorExact.agda
grep -q 'sourceIonicFluxSplits' DASHI/Biology/Physical/BiologicalElectrodiffusionTissueDonorExact.agda
grep -q 'hamming9Symmetric' DASHI/Biology/Physical/BiologicalRNA9HammingExact.agda
grep -q 'originalsOneSubstitution' DASHI/Biology/Physical/BiologicalRNA9HammingExact.agda
grep -q 'candidateTimeAdvances' DASHI/Biology/Physical/BiologicalAtomicMolecularHammingReuseExact.agda
grep -q 'sourceQualifiedCellObservation' \
  DASHI/Biology/Physical/SourceIndexedBiologicalCarrierExact.agda
grep -q 'withdrawalReopensModelCandidate' \
  DASHI/Biology/Physical/BiologicalEvidenceFeedbackFiniteExact.agda

# P0 source-owner presence gates; the real parallel checker below remains
# the kernel authority. These checks only prevent stale Golden imports.
grep -q 'lookupTransferAwayFromEndpoints' \
  DASHI/Biology/Physical/BiologicalSharedFiniteVectorTransferExact.agda
grep -q 'originalNativeBondUnchangedOutsideEndpoints' \
  DASHI/Biology/Physical/BiologicalSharedFiniteVectorTransferExact.agda
grep -q 'originalBondLocalSourceDebitIsPaid' \
  DASHI/Biology/Physical/BiologicalOriginal54BondSharedVectorExact.agda
grep -q 'everyChronologicalOriginalDirectedHistoryConserves' \
  DASHI/Biology/Physical/BiologicalOriginal54BondSharedVectorExact.agda
grep -q 'nativeHistoryLeavesUnvisitedVoxelUnchanged' \
  DASHI/Biology/Physical/BiologicalOriginal54BondSharedVectorExact.agda

grep -q 'originalFaceInjectionLeavesOtherVoxelUnchanged' \
  DASHI/Biology/Physical/Biological369CubicalBoundaryMaterialExact.agda
grep -q 'originalFaceDischargeLeavesOtherVoxelUnchanged' \
  DASHI/Biology/Physical/Biological369CubicalBoundaryMaterialExact.agda

# Source-owner gates for exact executed native quanta, geometry-paid
# distinctness, and signed one-step current. Kernel acceptance below
# remains authoritative; grep does not discharge a theorem.
grep -q 'lookupTransferSourcePaid' \
  DASHI/Biology/Physical/BiologicalSharedFiniteVectorTransferExact.agda
grep -q 'lookupTransferTargetReceivesActualSource' \
  DASHI/Biology/Physical/BiologicalSharedFiniteVectorTransferExact.agda
grep -q 'originalDirectedNativeEndpointsDistinct' \
  DASHI/Biology/Physical/BiologicalOriginal54BondSharedVectorExact.agda
grep -q 'originalNativeVoxelIncidenceBalance' \
  DASHI/Biology/Physical/BiologicalOriginal54BondSharedVectorExact.agda
grep -q 'original369SignedNativeOneStepContinuity' \
  DASHI/Biology/Physical/Biological369CubicalOpenSignedChargeExact.agda

python3 scripts/check_biological_history_future_quotient.py
python3 scripts/check_biological_spatial_stochastic.py
python3 scripts/check_biological_minimal_cube.py
python3 scripts/check_biological_all_neighbours.py
python3 scripts/biological_gocam_sbml_receipt_intake.py --self-test
python3 scripts/biological_si_kinetic_calibration.py --self-test
python3 scripts/biological_measured_genotype_holdout.py --self-test
python3 scripts/prepare_shine_dalgarno_measured.py --self-test
python3 scripts/check_original_dmsc_holdout.py --self-test
python3 scripts/check_original_dmsc_neutral_components.py --self-test
python3 scripts/check_original_dmsc_replicate_ranges.py --self-test
python3 scripts/check_original_measured_context_transfer.py --self-test
python3 scripts/check_biological_rna9_hamming.py
python3 scripts/check_original_dmsc_exact_replicate_bootstrap.py
python3 scripts/check_longitudinal_attractor_discrimination.py --self-test
python3 scripts/check_biological_parametric_minimal18.py
python3 scripts/check_biological_spatial_circulation.py
python3 scripts/biological_shared_spatial_finite_volume.py --self-test
python3 scripts/check_biological_signed_charge_27.py
python3 scripts/check_biological_369_pants_physical_seam.py
python3 scripts/check_biological_369_threeway_pants.py
python3 scripts/check_biological_369_face_exchange.py
python3 scripts/check_biological_369_open_signed_charge.py
python3 scripts/check_biological_369_local_charge_continuity.py

# Run the repository-owned parallel Agda checker, never an ad hoc local
# direct Agda invocation. Its exact-head result remains a separate receipt
# from these Python/Agda-owner presence checks.
if [ ! -x scripts/run_agda29_parallel_check.sh ]; then
  echo "FAIL CLOSED: repository parallel Agda checker is unavailable." >&2
  exit 2
fi
scripts/run_agda29_parallel_check.sh "$ROOT"
echo "REPOSITORY PARALLEL AGDA CHECKER COMPLETED: $ROOT"
echo "Publish exact-head checker receipt separately; no source-only promotion."
