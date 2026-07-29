#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

exec "$SCRIPT_DIR/run_agda29_parallel_check.sh" \
  DASHI/Physics/YangMills/BalabanClayGate4CanonicalBackgroundFibreWitnessExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4FlatWilsonActionPositivityExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4SU2HaarIdentityPositivityExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4FiniteCoerciveDeterminantPositivityExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4CanonicalReferenceFactorAssemblyExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4RationalPositiveMassReciprocalExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4CanonicalReferenceNormalizationExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4TCompensatedSixFactorBudgetExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4CanonicalCompensatedEquation189Exact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4HaarDeterminantRelativeLossReuseExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4FlatReferencePositiveWitnessExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4DyadicRunningCouplingConventionExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4BlockAveragingResidualSummabilityExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4SummableTailBudgetClosureExact.agda \
  DASHI/Physics/YangMills/BalabanClayT5ConditionedObservableLocalizationSummationExact.agda \
  DASHI/Physics/YangMills/BalabanClayT5PerScaleDecouplingClosureExact.agda \
  DASHI/Physics/YangMills/BalabanClayT5OSReconstructionCyclicityExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4Attachment252MechanismAuditExact.agda \
  DASHI/Physics/YangMills/BalabanClayGate4Validation.agda \
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerAdvance.agda \
  DASHI/Physics/YangMills/BalabanClayGate4AndNumericalAuditCompletionLedger.agda \
  DASHI/Physics/YangMills/BalabanClayGate4CurrentFrontierCompletionLedger.agda \
  DASHI/Physics/YangMills/BalabanClayBranchHeadReceiptSurface.agda \
  DASHI/Physics/YangMills/BalabanClayGate4CurrentFrontierReceipt.agda \
  DASHI/Physics/Closure/NSPeriodicOfficialCompletionRegression.agda
