module DASHI.Core.CapabilityReconstructionCostBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

data ReconstructionCoordinate : Set where
  namedSuccessor overlappingTeam preservedApparatus preservedRepository
  preservedNotebooks preservedCalibration preservedQualification
  preservedFailureHistory preservedConfiguration preservedAccess crossTraining
  documentedProcedure duplicateCapability rehiring recalibration requalification
  rediscovery scheduleSlip : ReconstructionCoordinate

data ReconstructionCostClass : Set where low moderate high unknown : ReconstructionCostClass

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
    namedSuccessorImpliesLowCarrierReconstructionCostIsFalse : namedSuccessorImpliesLowCarrierReconstructionCost ≡ false
    projectContinuityImpliesSameCarrierTransfer : Bool
    projectContinuityImpliesSameCarrierTransferIsFalse : projectContinuityImpliesSameCarrierTransfer ≡ false
    noLocatedRebuildImpliesNoRebuild : Bool
    noLocatedRebuildImpliesNoRebuildIsFalse : noLocatedRebuildImpliesNoRebuild ≡ false
    explicitRecalibrationOrRequalificationCanEvidenceReconstructionCost : Bool
    explicitRecalibrationOrRequalificationCanEvidenceReconstructionCostIsTrue : explicitRecalibrationOrRequalificationCanEvidenceReconstructionCost ≡ true

canonicalReconstructionCostBoundary : ReconstructionCostBoundary
canonicalReconstructionCostBoundary = reconstruction-cost-boundary false refl false refl false refl true refl

data ReconstructionReverseTarget : Set where
  acquireNamedSuccessor acquireOverlappingTeam acquireApparatusCustody
  acquireRepositoryCustody acquireNotebookCustody acquireCalibrationTransfer
  acquireQualificationTransfer acquireFailureHistoryTransfer
  acquireConfigurationTransfer acquireAccessTransfer acquireCrossTraining
  acquireProcedureCompleteness acquireRecalibrationEvidence
  acquireRequalificationEvidence acquireRebuildScheduleImpact : ReconstructionReverseTarget
