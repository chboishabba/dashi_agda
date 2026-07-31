#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

bash "$SCRIPT_DIR/check_gate4_frontier_static.sh"

exec "$SCRIPT_DIR/run_agda29_parallel_check.sh" \
  DASHI/Physics/YangMills/BalabanClayGate4CanonicalBackgroundFibreWitnessExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4FlatWilsonActionPositivityExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4SU2HaarIdentityPositivityExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4FiniteCoerciveDeterminantPositivityExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4FiniteCoercivityInverseNormExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4IpsenRehmanDeterminantLossExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4IpsenRehmanCompensatedTAdapterExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4CanonicalReferenceFactorAssemblyExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4RationalPositiveMassReciprocalExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4CanonicalReferenceNormalizationExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4TCompensatedSixFactorBudgetExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4CanonicalCompensatedEquation189Exact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4HaarDeterminantRelativeLossReuseExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4FlatReferencePositiveWitnessExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4FiniteVisitedSetBFSAlgorithmExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4FiniteVisitedSetBFSParentCorrectnessExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PeriodicExecutableBFSInstantiationExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4StrongBFSParentCertificateExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4BFSAdjacentLayerShortestPathExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4DyadicRunningCouplingConventionExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4FiniteKernelSchurBlockAdjointExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryAveragingDimensionAuditExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryBibliographyChainExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryAveragingLocalityExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryQkFiniteKernelBudgetExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryQkAdjointColumnExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryQkSchurBridgeExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryQkPhysicalSchurAssemblyExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4FiniteWeightedSchurBlockAdjointExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryQkWeightedSchurExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PeriodicQkSupportEnumerationExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PeriodicQkUniformSupportBoundsExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PeriodicQkPrimaryKernelInstantiationExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PeriodicQkWeightedSchurInstantiationExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4ConstrainedMinimizerProjectionExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4ConstrainedHessianRestrictionExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryBetaFiniteDifferenceExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryAveragingTrancheLedger.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryAveragingTrancheReceipt.agda \
  DASHI/Physics/YangMills/BalabanClayGate4PrimaryAveragingCurrentFrontierExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4BlockAveragingResidualSummabilityExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4SummableTailBudgetClosureExact.agda \
  DASHI/Physics/YangMills/BalabanClayT5KoteckyPreissTwoWeightPrimaryExact.agda \
  DASHI/Physics/YangMills/BalabanClayT5PhysicalTwoWeightKoteckyPreissExact.agda \
  DASHI/Physics/YangMills/BalabanClayT5ConditionedObservableLocalizationSummationExact.agda \
  DASHI/Physics/YangMills/BalabanClayT5PerScaleDecouplingClosureExact.agda \
  DASHI/Physics/YangMills/BalabanClayT5AnisotropyPolymerSummationExact.agda \
  DASHI/Physics/YangMills/BalabanClayT5OSReconstructionCyclicityExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4Attachment252MechanismAuditExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4July2026ResearchUpdateExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4July2026ResearchUpdateLedger.agda \
  DASHI/Physics/YangMills/BalabanClayGate4AnisotropyBlockAndCriterionProvenanceExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4HighAlphaTrancheLedger.agda \
  DASHI/Physics/YangMills/BalabanClayGate4HighAlphaTrancheReceipt.agda \
  DASHI/Physics/YangMills/BalabanClayGate4Validation.agda \
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerAdvance.agda \
  DASHI/Physics/YangMills/BalabanClayGate4AndNumericalAuditCompletionLedger.agda \
  DASHI/Physics/YangMills/BalabanClayGate4CurrentFrontierCompletionLedger.agda \
  DASHI/Physics/YangMills/BalabanClayBranchHeadReceiptSurface.agda \
  DASHI/Physics/YangMills/BalabanClayGate4CurrentFrontierReceipt.agda \
  DASHI/Physics/Closure/NSPeriodicOfficialCompletionRegression.agda
