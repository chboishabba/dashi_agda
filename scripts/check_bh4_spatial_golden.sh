#!/usr/bin/env bash
# Kitzerow BH4 spatial physical max-cut: exact source regression + native
# repo-owned parallel Agda Golden proof gate. No direct Agda invocation.
set -euo pipefail
cd "$(dirname "$0")/.."

ROOT=DASHI/Biology/KitzerowBH4EvidenceEverything.agda
# Default mode checks synthetic finite regressions and the Agda Golden,
# but does NOT certify missing original Rhea or physiological evidence.
# Opt-in strict source mode never accepts an incomplete original dataset.
if [ "${BH4_REQUIRE_SOURCE_PAID:-0}" = "1" ]; then
  test -s artifacts/biology/rhea-kitzerow-bh4-reactions.json || {
    echo "FAIL CLOSED: strict BH4 source requires original Rhea certificate" >&2
    exit 2
  }
  for required in BH4_ORIGINAL_PARAMETERS_PATH BH4_ORIGINAL_CANDIDATE_PATH BH4_ORIGINAL_ASSAY_PATH; do
    test -n "${!required:-}" && test -s "${!required}" || {
      echo "FAIL CLOSED: strict BH4 source requires $required input" >&2
      exit 2
    }
  done
fi
MODULES=(
  DASHI/Biology/Molecular/BH4PanelStoichiometricMatrixExact.agda
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

# Original 29x12 conditional reaction history owner must remain in the
# existing Golden import and contain the complete CHNOP/signed proofs.
grep -q 'original29x12SpatialReactionBalance' \
  DASHI/Biology/Molecular/BH4PanelStoichiometricMatrixExact.agda
grep -q 'original29x12SpatialSignedChargeBalance' \
  DASHI/Biology/Molecular/BH4PanelStoichiometricMatrixExact.agda
grep -q 'original29x12SpatialAllHistoryCHNOPBalance' \
  DASHI/Biology/Molecular/BH4PanelStoichiometricMatrixExact.agda
grep -q 'original29x12SpatialAllHistorySignedChargeBalance' \
  DASHI/Biology/Molecular/BH4PanelStoichiometricMatrixExact.agda
grep -q 'import DASHI.Biology.Molecular.BH4PanelStoichiometricMatrixExact' \
  DASHI/Biology/KitzerowBH4EvidenceEverything.agda

python3 scripts/check_bh4_allocator_future_observer.py
python3 scripts/check_bh4_spatial_circulation.py
python3 scripts/check_bh4_shared_redox_dynamics.py
python3 scripts/check_bh4_original_qdpr_spatial_reaction.py
python3 scripts/bh4_original_qdpr_spatial_finite_volume.py --self-test
# Syntax must be validated before executing the source-aware original
# Python owner. This catches literal escaped-newline source corruption
# even when the original 29x12 certificate is not mounted.
python3 -c 'import ast, pathlib; p=pathlib.Path("scripts/check_bh4_original_panel_spatial_events.py"); ast.parse(p.read_text(encoding="utf-8"), filename=str(p))'
# Check source-release drift diagnostics offline. Live acquisition requires
# --require-rhea-release when reproducing a particular historical vintage.
python3 scripts/acquire_rhea_chebi_bh4_reactions.py --release-guard-self-test
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
  BH4_SOURCE_ARGS=(
    --certificate artifacts/biology/rhea-kitzerow-bh4-reactions.json
    --parameters "$BH4_ORIGINAL_PARAMETERS_PATH"
    --candidate "$BH4_ORIGINAL_CANDIDATE_PATH"
  )
  if [ -n "${BH4_ORIGINAL_ASSAY_PATH:-}" ]; then
    test -f "$BH4_ORIGINAL_ASSAY_PATH"
    BH4_SOURCE_ARGS+=(--assay "$BH4_ORIGINAL_ASSAY_PATH")
  else
    echo "OPEN MATCHED ASSAY GATE: no original longitudinal assay linked; flux remains algebraic only" >&2
  fi
  python3 scripts/check_bh4_original_panel_spatial_events.py "${BH4_SOURCE_ARGS[@]}"
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
if [ "${BH4_REQUIRE_SOURCE_PAID:-0}" = "1" ]; then
  echo "BH4 SOURCE-QUALIFIED INPUT CHECKS AND NATIVE GOLDEN COMPLETED; independent rate and causal verification remain OPEN."
else
  echo "BH4 FINITE/AGDA GOLDEN COMPLETED; original 29x12 source and physical rates remain separate OPEN gates."
fi
