#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

bash "$SCRIPT_DIR/check_gate4_frontier_static.sh"

FILES=(
  DASHI/Physics/YangMills/BalabanClayGate4SevenGroupResearchAuditExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4CMP109ProjectedEndpointBlocksExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4CMP109LiteralIdentificationAssemblyExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4LocalityFrechetSupportExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4CMP109ConstantWeightSchurExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiniteWeightedSchurCertificateExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4KochWittwerContractionResidualExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiveChannelSumSelfAdjointExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4T3FiveChannelSumReuseExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PeriodicTreeGaugeCoordinatesExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PeriodicTreeGaugeFiniteBasisExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4T3TreeGaugeSpectralDeterminantExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4HRBetaHalfRemainderDominanceExact.agda

  DASHI/Physics/YangMills/BalabanClayGate4CMP109PrintedPathFormulaExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PeriodicPathWordExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PeriodicWordPathConstructionExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4CMP109PrintedMapInstantiationExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiniteHolonomyDerivativeExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4SU2DexpInverseClosedFormExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4CMP109SupportOverlapCompletionExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiniteWeightedAdjointFubiniExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiniteWeightedAdjointFormulaExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiniteWeightedSchurCertificateCompletionExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4SpanningTreeGaugeSliceExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PeriodicTreeGaugeCanonicalFreeBasisExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PeriodicTreeGaugeSU2FreeBasisExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiniteCoordinateMatrixEquivalenceExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiniteCoordinateMatrixCompositionExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiniteDeterminantFactorizationExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiniteSimilaritySpectrumDeterminantExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiniteSpectrumDeterminantCompletionExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiniteProofEngineeringCompletionLedger.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiniteProofEngineeringValidation.agda
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerFiniteProofEngineeringAdvance.agda

  DASHI/Physics/YangMills/BalabanClayGate4SevenGroupFrontierLedger.agda
  DASHI/Physics/YangMills/BalabanClayGate4SevenGroupFrontierReceipt.agda
  DASHI/Physics/YangMills/BalabanClayGate4SevenGroupValidation.agda
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerSevenGroupAdvance.agda
)

for relative in "${FILES[@]}"; do
  file="$ROOT_DIR/$relative"
  [[ -f "$file" ]] || {
    echo "missing seven-group frontier file: $relative" >&2
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
