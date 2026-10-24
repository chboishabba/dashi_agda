#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
printf 'HEAD=%s\n' "$(git rev-parse HEAD)"
if ! command -v agda >/dev/null 2>&1; then
  echo 'ERROR: Agda kernel unavailable. No claim of typecheck is permitted.' >&2
  exit 127
fi
agda --version
targets=(
  DASHI/Mathematics/Topology/AlexanderHornedC3AmbientRotationExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3SatellitePlacementExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3JordanActionExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3FiniteVOAActorExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3FiniteStageExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3ComplementActionExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3OrbitSolidExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3ExteriorBridge.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3CharactersExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3OuterDetectorExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3FreeFactorDetectorExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedAbelianHolonomyBIDIExact.agda
)
for path in "${targets[@]}"; do
  echo "AGDA_CHECK_START $path"
  if [[ -n "${AGDA_STDLIB_SRC_29:-}" || -n "${AGDA_STDLIB_SRC:-}" ]]; then
    stdlib="${AGDA_STDLIB_SRC_29:-${AGDA_STDLIB_SRC}}"
    [[ -d "$stdlib/src" ]] && stdlib="$stdlib/src"
    agda --no-libraries --no-default-libraries -i . -i "$stdlib" "$path"
  else
    agda -i . -l standard-library "$path"
  fi
  echo "AGDA_CHECK_PASS $path"
done
echo "AGDA_EXACT_HEAD_ALL_PASS $(git rev-parse HEAD)"
