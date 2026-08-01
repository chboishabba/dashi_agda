#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

bash "$SCRIPT_DIR/check_gate4_seven_group.sh"

FILES=(
  DASHI/Physics/YangMills/BalabanClayGate4CMP109CenteredOddBlockCarrierExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4CMP109CenteredEndpointCertificateExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4CMP109CenteredBlockEndpointCertificateExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4CMP109CenteredTorusBijectionExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4CMP109CenteredExecutableGeometryExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4DimockTrilogyResearchAuditExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4DimockNormalizedPolymerReblockingExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4DimockLargeFieldSuppressionExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4DimockClusterWithHolesLocalInfluenceExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4DimockRootedDecayVolumeExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4DimockConnectedActivityStabilityExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4SU2FixedRadiusEnvelopeExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalOperatorChannelIdentificationExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4HRBetaDimockLocalizationAdapterExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalClosureRound3IntegratedExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalClosureRound3Ledger.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalClosureRound3Receipt.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalClosureRound3Validation.agda
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerPhysicalClosureRound3Advance.agda
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerSevenGroupAdvance.agda
)

for relative in "${FILES[@]}"; do
  file="$ROOT_DIR/$relative"
  [[ -f "$file" ]] || {
    echo "missing Gate-4 round-three file: $relative" >&2
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
