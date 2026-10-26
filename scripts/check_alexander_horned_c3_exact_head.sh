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
  DASHI/Mathematics/Topology/AlexanderHornedTorsionFreeStageTransportExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedBinaryPadicCylinderExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3ClopenCylinderMassExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3ChronologicalClopenBridgeExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedQuaternionC3SpinExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedSpin360720Exact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3SpinLiftSplitExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3MaschkeR3Exact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3Mod3JordanExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3MaschkeReynoldsExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3ModularJordanF3Exact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3R3HodgeEquivarianceExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3SpinCyclotomicIntertwinerExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3F7FullActorMaschkeExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedProPSolvableBlindExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedMixedPrimeCRTWeldExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedBinaryIcosahedralSpinSignBidiExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedPadicCongruenceNoGoExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedSpinVOAFactorFunctorExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedNonabelianRegularPadicReuseExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedBinaryTernaryExistingCodecWeldExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedOreFiniteTargetExtensionExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedA5C3CharacterRestrictionExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedA5C3RestrictionWeldExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3FiniteVOAActorExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3VOAModeLiftExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedC3VOAKernelBidiExact.agda
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
