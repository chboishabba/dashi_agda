#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

FILES=(
  DASHI/Physics/YangMills/BalabanClayGate4FiniteVisitedSetBFSAlgorithmExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiniteVisitedSetBFSParentCorrectnessExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PeriodicExecutableBFSInstantiationExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4StrongBFSParentCertificateExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4BFSAdjacentLayerShortestPathExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiniteCoercivityInverseNormExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4IpsenRehmanDeterminantLossExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4IpsenRehmanCompensatedTAdapterExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4DyadicRunningCouplingConventionExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiniteKernelSchurBlockAdjointExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryAveragingDimensionAuditExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryBibliographyChainExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryAveragingLocalityExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryQkFiniteKernelBudgetExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryQkAdjointColumnExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryQkSchurBridgeExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryQkPhysicalSchurAssemblyExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiniteWeightedSchurBlockAdjointExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryQkWeightedSchurExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PeriodicQkSupportEnumerationExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PeriodicQkUniformSupportBoundsExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PeriodicQkPrimaryKernelInstantiationExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4ConstrainedMinimizerProjectionExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4ConstrainedHessianRestrictionExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryBetaFiniteDifferenceExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryAveragingTrancheLedger.agda
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryAveragingTrancheReceipt.agda
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryAveragingCurrentFrontierExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4BlockAveragingResidualSummabilityExact.agda
  DASHI/Physics/YangMills/BalabanClayT5KoteckyPreissTwoWeightPrimaryExact.agda
  DASHI/Physics/YangMills/BalabanClayT5PhysicalTwoWeightKoteckyPreissExact.agda
  DASHI/Physics/YangMills/BalabanClayT5AnisotropyPolymerSummationExact.agda
  DASHI/Physics/YangMills/BalabanClayT5AlternativeHarrisMixingAuditExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4Attachment252MechanismAuditExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4July2026ResearchUpdateExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4July2026ResearchUpdateLedger.agda
  DASHI/Physics/YangMills/BalabanClayGate4AnisotropyBlockAndCriterionProvenanceExact.agda
  DASHI/Physics/YangMills/BalabanClayMassGapClaimEcosystemQuarantineExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4HighAlphaTrancheLedger.agda
  DASHI/Physics/YangMills/BalabanClayGate4HighAlphaTrancheReceipt.agda
  DASHI/Physics/YangMills/BalabanClayGate4Validation.agda
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerAdvance.agda
)

status=0
for relative in "${FILES[@]}"; do
  file="$ROOT_DIR/$relative"
  if [[ ! -f "$file" ]]; then
    echo "missing Gate-4 frontier file: $relative" >&2
    status=1
    continue
  fi

  if grep -nE '^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+[^[:space:]]*/' "$file"; then
    echo "malformed slash-separated Agda module import in $relative" >&2
    status=1
  fi

  if grep -nE '=[[:space:]]*(quarantined|verifiedLiterature)[[:space:]]*$' "$file"; then
    echo "obsolete ProofLevel constructor in $relative" >&2
    status=1
  fi

  if grep -nE '\{!|!\}' "$file"; then
    echo "explicit Agda hole in $relative" >&2
    status=1
  fi

  if grep -nE '^[[:space:]]*postulate([[:space:]]|$)' "$file"; then
    echo "postulate introduced on the focused Gate-4 frontier in $relative" >&2
    status=1
  fi
done

exit "$status"
