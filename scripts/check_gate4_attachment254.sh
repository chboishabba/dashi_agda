#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

bash "$SCRIPT_DIR/check_gate4_frontier_static.sh"

EXTRA_FILES=(
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalAveragingConventionSelectionExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalWeightedL2NormalizationExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4WeightedSchurSummableSlackReuseExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4T3SelfAdjointFormNormReuseExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiveChannelSelfAdjointOperatorBoundExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4T3FiveChannelSelfAdjointReuseExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4Attachment254IntegratedLedger.agda
  DASHI/Physics/YangMills/BalabanClayGate4Attachment254IntegratedReceipt.agda
  DASHI/Physics/YangMills/BalabanClayGate4Attachment254Validation.agda
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerAttachment254Advance.agda
)

for relative in "${EXTRA_FILES[@]}"; do
  file="$ROOT_DIR/$relative"
  [[ -f "$file" ]] || {
    echo "missing attachment-254 file: $relative" >&2
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

exec "$SCRIPT_DIR/run_agda29_parallel_check.sh" \
  DASHI/Physics/YangMills/BalabanClayGate4Attachment254ResearchAuditExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalAveragingConventionSelectionExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4SU2PrincipalLogBallExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PeriodicEndpointBlockPredicateExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalWeightedL2NormalizationExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4SelfAdjointFormOperatorNormExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4FiniteHermitianRayleighSpectrumExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4NearContractionSummableSlackExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4WeightedSchurSummableSlackReuseExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4IpsenRehmanPrimaryCorollary214Exact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4BetaMonteCarloConventionAuditExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryCouplingAdmissibilityInductionExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4T3SelfAdjointFormNormReuseExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4FiveChannelSelfAdjointOperatorBoundExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4T3FiveChannelSelfAdjointReuseExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4Attachment254CompletionLedger.agda \
  DASHI/Physics/YangMills/BalabanClayGate4Attachment254CompletionReceipt.agda \
  DASHI/Physics/YangMills/BalabanClayGate4Attachment254IntegratedLedger.agda \
  DASHI/Physics/YangMills/BalabanClayGate4Attachment254IntegratedReceipt.agda \
  DASHI/Physics/YangMills/BalabanClayGate4Attachment254Validation.agda \
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerAttachment254Advance.agda
