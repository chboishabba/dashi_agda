#!/usr/bin/env bash
# Kitzerow BH4 spatial physical max-cut: exact source regression + native
# repo-owned parallel Agda Golden proof gate. No direct Agda invocation.
set -euo pipefail
cd "$(dirname "$0")/.."

ROOT=DASHI/Biology/KitzerowBH4EvidenceEverything.agda
MODULES=(
  DASHI/Biology/BH4SharedSourceTargetRedoxDynamicsExact.agda
  DASHI/Biology/BH4SpatialConnectivityCirculationExact.agda
  DASHI/Biology/BH4PNPSamePhysicalHistoryBridgeExact.agda
  DASHI/Biology/BH4CatalyticTurnoverFutureCountermodelExact.agda
  DASHI/Biology/BH4AllocatorFutureObservationCountermodelExact.agda
)
for path in "${MODULES[@]}"; do
  test -s "$path"
  if grep -vE '^[[:space:]]*--' "$path" |
     grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!!\}|--allow-unsolved-metas|primTrustMe'; then
    echo "Unsafe escape in spatial biology Agda owner $path" >&2
    exit 1
  fi
done

python3 scripts/check_bh4_allocator_future_observer.py
python3 scripts/check_bh4_spatial_circulation.py
python3 scripts/check_bh4_shared_redox_dynamics.py
python3 scripts/check_bh4_spatial_measurement_payment.py --self-test

if [ ! -f scripts/run_agda29_parallel_check.sh ]; then
  echo "FAIL CLOSED: native parallel_checker wrapper missing" >&2
  exit 2
fi
bash scripts/run_agda29_parallel_check.sh "$ROOT"
echo "BH4 SPATIAL GOLDEN CHECKER COMPLETED; exact-head receipt required."
