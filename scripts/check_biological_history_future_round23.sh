#!/usr/bin/env bash
# Standalone gate; independent parallel_checker acceptance is separate.
set -euo pipefail
cd "$(dirname "$0")/.."

ROOT=DASHI/EverythingBiologicalHistoryFutureRound23.agda
MODULES=(
  DASHI/Biology/Physical/BiologicalHistoryFutureQuotientExact.agda
  DASHI/Biology/Physical/BiologicalEvidenceFeedbackFiniteExact.agda
  DASHI/Biology/Physical/SourceIndexedBiologicalCarrierExact.agda
  DASHI/Biology/Physical/BiologicalFuturePartitionCompilerExact.agda
  DASHI/Biology/Physical/BiologicalStochasticFutureLumpingExact.agda
  DASHI/Biology/Physical/BiologicalCoupledTissueCubeExact.agda
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
grep -q 'initialAllTracesPreserveBiologicalProjection' \
  DASHI/Biology/Physical/BiologicalCoupledTissueCubeExact.agda
grep -q 'sourceQualifiedCellObservation' \
  DASHI/Biology/Physical/SourceIndexedBiologicalCarrierExact.agda
grep -q 'withdrawalReopensModelCandidate' \
  DASHI/Biology/Physical/BiologicalEvidenceFeedbackFiniteExact.agda

python3 scripts/check_biological_history_future_quotient.py
python3 scripts/biological_gocam_sbml_receipt_intake.py --self-test
python3 scripts/biological_si_kinetic_calibration.py --self-test
python3 scripts/biological_measured_genotype_holdout.py --self-test
python3 scripts/prepare_shine_dalgarno_measured.py --self-test

if ! command -v agda >/dev/null 2>&1; then
  echo "FAIL CLOSED: Agda unavailable; kernel and parallel_checker acceptance pending." >&2
  exit 2
fi
agda -i . -i src "$ROOT"
echo "LOCAL AGDA TYPECHECK ACCEPTED: $ROOT"
echo "Independent exact-head parallel_checker receipt remains separately required."
