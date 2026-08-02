#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

bash "$SCRIPT_DIR/check_gate4_physical_round5_final.sh"

FILES=(
  DASHI/Physics/YangMills/BalabanClayGate4NestedThresholdCompatibilityExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4ContourSwapDiameterExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4CMP109SmallDiameterFromSwapsExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4BishopHalfRadiusRationalConstantsExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FederbushAsymmetricQuarterBudgetExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4BackgroundGaugeMixedNormExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PlaquetteDerivativeCombinatoricsExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4LocalWilsonThirdDerivativeExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4IntegratedGaussianFluctuationExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4ROperationPrimarySourceAuditExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PointwiseSmallFactorEntropyBridgeExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4OscillationAnimalInfluenceExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4ThreeWayRemainderDecompositionExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4WeakeningDependencyGraphExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4ConstraintNormalInversePerturbationExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiveChannelSmallFieldRadiusExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4SU2HaarJacobianDefectExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4WilsonAnimalEntropyLedgerExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiveActivityEngineOwnershipExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalClosureRound6ExactCutset.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalClosureRound6Ledger.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalClosureRound6Receipt.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalClosureRound6Validation.agda
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerPhysicalClosureRound6Advance.agda
  DASHI/Physics/YangMills/BalabanClayGate4SevenGroupValidation.agda
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerSevenGroupAdvance.agda
)

for relative in "${FILES[@]}"; do
  file="$ROOT_DIR/$relative"
  [[ -f "$file" ]] || {
    echo "missing Gate-4 round-six file: $relative" >&2
    exit 1
  }

  if grep -nE '^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+[^[:space:]]*/' "$file"; then
    echo "malformed slash-separated Agda import in $relative" >&2
    exit 1
  fi

  if grep -nE '=[[:space:]]*(quarantined|verifiedLiterature)[[:space:]]*$' "$file"; then
    echo "obsolete ProofLevel constructor in $relative" >&2
    exit 1
  fi

  if grep -nE '\{!|!\}' "$file"; then
    echo "explicit Agda hole in $relative" >&2
    exit 1
  fi

  if grep -nE '^[[:space:]]*postulate([[:space:]]|$)' "$file"; then
    echo "postulate introduced in $relative" >&2
    exit 1
  fi
done

exec "$SCRIPT_DIR/run_agda29_parallel_check.sh" "${FILES[@]}"
