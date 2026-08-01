#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

bash "$SCRIPT_DIR/check_gate4_physical_round3.sh"

FILES=(
  DASHI/Physics/YangMills/BalabanClayGate4CMP109PhysicalScaleGeometryExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4CMP109SiteWeightIdentificationExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4CMP109ContourMultiplicityExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4SU2PauliNormConventionExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4SU2HalfRadiusScalarEnvelopeExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4ConservativeDyadicNewtonBudgetExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalOperatorChannelIdentificationExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalHessianFiveChannelDecompositionExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalHessianFactorizedSelfAdjointExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalHessianFromFactorizationsExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiveChannelSixteenthBudgetExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4GaugeTaylorLocalizationExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4GaugeLargeFieldPenaltyExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4GaugeRandomWalkLocalizationExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4GaugeClusterLocalInfluenceExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4GaugeRootedEntropyDecayExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4GaugeHRBetaFiveActivityAllocationExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalClosureRound4IntegratedExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalClosureRound4Ledger.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalClosureRound4Receipt.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalClosureRound4Validation.agda
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerPhysicalClosureRound4Advance.agda
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerSevenGroupAdvance.agda
)

for relative in "${FILES[@]}"; do
  file="$ROOT_DIR/$relative"
  [[ -f "$file" ]] || {
    echo "missing Gate-4 round-four file: $relative" >&2
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
