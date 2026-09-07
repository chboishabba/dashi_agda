module DASHI.Core.CapabilityReconstructionCostBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CAPABILITY RECONSTRUCTION COST, BIDI
--
-- Separates impressive science from the practical cost of restoring an
-- application capability after retirement, departure, death, reorganisation,
-- access change, or loss of a particular holder.
------------------------------------------------------------------------

data ReconstructionCoordinate : Set where
  namedSuccessor : ReconstructionCoordinate
  overlappingTeam : ReconstructionCoordinate
  preservedApparatus : ReconstructionCoordinate
  preservedRepository : ReconstructionCoordinate
  preservedNotebooks : ReconstructionCoordinate
  preservedCalibration : ReconstructionCoordinate
  preservedQualification : ReconstructionCoordinate
  preservedFailureHistory : ReconstructionCoordinate
  preservedConfiguration : ReconstructionCoordinate
  preservedAccess : ReconstructionCoordinate
  crossTraining : ReconstructionCoordinate
  documentedProcedure : ReconstructionCoordinate
  duplicateCapability : ReconstructionCoordinate
  rehiring : ReconstructionCoordinate
  recalibration : ReconstructionCoordinate
  requalification : ReconstructionCoordinate
  rediscovery : ReconstructionCoordinate
  scheduleSlip : ReconstructionCoordinate


data ReconstructionCostClass : Set where
  low : ReconstructionCostClass
  moderate : ReconstructionCostClass
  high : ReconstructionCostClass
  unknown : ReconstructionCostClass


record ReconstructionCostProfile : Set where
  constructor reconstruction-cost-profile
  field
    domain : String
    continuityReceipts : List ReconstructionCoordinate
    rebuildReceipts : List ReconstructionCoordinate
    costClass : ReconstructionCostClass
    sourceReference : String
    boundedReading : String

open ReconstructionCostProfile public

record ReconstructionCostBoundary : Set where
  constructor reconstruction-cost-boundary
  field
    namedSuccessorImpliesLowCarrierReconstructionCost : Bool
    namedSuccessorImpliesLowCarrierReconstructionCostIsFalse :
      namedSuccessorImpliesLowCarrierReconstructionCost ≡ false
    projectContinuityImpliesSameCarrierTransfer : Bool
    projectContinuityImpliesSameCarrierTransferIsFalse :
      projectContinuityImpliesSameCarrierTransfer ≡ false
    noLocatedRebuildImpliesNoRebuild : Bool
    noLocatedRebuildImpliesNoRebuildIsFalse : noLocatedRebuildImpliesNoRebuild ≡ false
    explicitRecalibrationOrRequalificationCanEvidenceReconstructionCost : Bool
    explicitRecalibrationOrRequalificationCanEvidenceReconstructionCostIsTrue :
      explicitRecalibrationOrRequalificationCanEvidenceReconstructionCost ≡ true

canonicalReconstructionCostBoundary : ReconstructionCostBoundary
canonicalReconstructionCostBoundary = reconstruction-cost-boundary
  false refl
  false refl
  false refl
  true refl

data ReconstructionReverseTarget : Set where
  acquireNamedSuccessor : ReconstructionReverseTarget
  acquireOverlappingTeam : ReconstructionReverseTarget
  acquireApparatusCustody : ReconstructionReverseTarget
  acquireRepositoryCustody : ReconstructionReverseTarget
  acquireNotebookCustody : ReconstructionReverseTarget
  acquireCalibrationTransfer : ReconstructionReverseTarget
  acquireQualificationTransfer : ReconstructionReverseTarget
  acquireFailureHistoryTransfer : ReconstructionReverseTarget
  acquireConfigurationTransfer : ReconstructionReverseTarget
  acquireAccessTransfer : ReconstructionReverseTarget
  acquireCrossTraining : ReconstructionReverseTarget
  acquireProcedureCompleteness : ReconstructionReverseTarget
  acquireRecalibrationEvidence : ReconstructionReverseTarget
  acquireRequalificationEvidence : ReconstructionReverseTarget
  acquireRebuildScheduleImpact : ReconstructionReverseTarget
