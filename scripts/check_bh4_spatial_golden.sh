#!/usr/bin/env bash
# Kitzerow BH4 spatial physical max-cut: exact source regression + native
# repo-owned parallel Agda Golden proof gate. No direct Agda invocation.
set -euo pipefail
cd "$(dirname "$0")/.."

ROOT=DASHI/Biology/KitzerowBH4EvidenceEverything.agda
MODULES=(
  DASHI/Biology/BH4OneMoleculeSpatialFutureMinimalityExact.agda
  DASHI/Biology/BH4SpatialOriginalQDPRStoichiometryExact.agda
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
python3 scripts/check_bh4_original_qdpr_spatial_reaction.py
python3 scripts/bh4_original_qdpr_spatial_finite_volume.py --self-test
# Syntax must be validated before executing the source-aware original
# Python owner. This catches literal escaped-newline source corruption
# even when the original 29x12 certificate is not mounted.
python3 -c 'import ast, pathlib; p=pathlib.Path("scripts/check_bh4_original_panel_spatial_events.py"); ast.parse(p.read_text(encoding="utf-8"), filename=str(p))'
python3 scripts/check_bh4_original_panel_spatial_events.py --self-test
# Real 29×12 check requires the source-acquired certificate; absence
# remains an explicit physical/source residual, not a synthetic payment.
if [ -f artifacts/biology/rhea-kitzerow-bh4-reactions.json ]; then
  python3 scripts/check_bh4_original_panel_spatial_events.py \
    --certificate artifacts/biology/rhea-kitzerow-bh4-reactions.json
else
  echo "OPEN SOURCE GATE: original 29×12 acquired Rhea certificate not mounted; synthetic QDPR self-test only" >&2
fi
# Optional strictly source-paid original 29x12 quantitative witness.
# Do NOT auto-promote a synthetic event fixture into measured kinetics.
# Caller must supply both source-bound original inputs explicitly.
if [ -n "${BH4_ORIGINAL_PARAMETERS_PATH:-}" ] ||
   [ -n "${BH4_ORIGINAL_CANDIDATE_PATH:-}" ]; then
  test -f "${BH4_ORIGINAL_PARAMETERS_PATH:?Original parameter receipt required}"
  test -f "${BH4_ORIGINAL_CANDIDATE_PATH:?Original candidate receipt required}"
  test -f artifacts/biology/rhea-kitzerow-bh4-reactions.json
  python3 scripts/check_bh4_original_panel_spatial_events.py \
    --certificate artifacts/biology/rhea-kitzerow-bh4-reactions.json \
    --parameters "$BH4_ORIGINAL_PARAMETERS_PATH" \
    --candidate "$BH4_ORIGINAL_CANDIDATE_PATH"
else
  echo "OPEN PHYSICAL RATE GATE: no original quantitative candidate and complete source-paid bounds supplied" >&2
fi

python3 scripts/check_bh4_one_molecule_future_minimality.py
python3 scripts/check_bh4_spatial_measurement_payment.py --self-test

if [ ! -f scripts/run_agda29_parallel_check.sh ]; then
  echo "FAIL CLOSED: native parallel_checker wrapper missing" >&2
  exit 2
fi
bash scripts/run_agda29_parallel_check.sh "$ROOT"
echo "BH4 SPATIAL GOLDEN CHECKER COMPLETED; exact-head receipt required."
