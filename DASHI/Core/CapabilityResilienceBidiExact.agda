module DASHI.Core.CapabilityResilienceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CAPABILITY RESILIENCE, BIDI
--
-- Criticality is not only about what a person knew.  It is also about how well
-- the organisation can preserve and reconstruct the application transformation
-- when a person leaves, dies, disappears, is reassigned, or loses access.
------------------------------------------------------------------------

data ResilienceCoordinate : Set where
  namedSuccessor
  overlappingTeam
  standardOperatingProcedures
  notebooksOrRepositories
  configurationManagement
  calibrationArchive
  qualificationArchive
  failureHistoryArchive
  hardwareCustodyContinuity
  accessTransfer
  crossTraining
  externalReplication
  : ResilienceCoordinate

data ResilienceState : Set where
  sourceBacked
  partial
  notLocated
  knownAbsent
  : ResilienceState

record ResilienceReceipt : Set where
  constructor resilience-receipt
  field
    applicationObject : String
    coordinate : ResilienceCoordinate
    state : ResilienceState
    sourceReference : String
    boundedReading : String

open ResilienceReceipt public

record CapabilityResilienceProfile : Set where
  constructor capability-resilience-profile
  field
    applicationObject : String
    receipts : List ResilienceReceipt
    profileReference : String
    boundedClaim : String

open CapabilityResilienceProfile public

data ResilienceReverseTarget : Set where
  acquireNamedSuccessor
  acquireOverlapPeriod
  acquireSOPCoverage
  acquireNotebookRepositoryCustody
  acquireConfigManagementHistory
  acquireCalibrationArchive
  acquireQualificationArchive
  acquireFailureArchive
  acquireHardwareTransfer
  acquireAccessTransfer
  acquireCrossTrainingEvidence
  acquireExternalReproduction
  : ResilienceReverseTarget

record ResilienceBoundary : Set where
  constructor resilience-boundary
  field
    projectContinuationImpliesCapabilityResilience : Bool
    projectContinuationImpliesCapabilityResilienceIsFalse : projectContinuationImpliesCapabilityResilience ≡ false
    namedSuccessorImpliesCompleteTacitTransfer : Bool
    namedSuccessorImpliesCompleteTacitTransferIsFalse : namedSuccessorImpliesCompleteTacitTransfer ≡ false
    strongArchivesCanReduceReplacementDifficulty : Bool
    strongArchivesCanReduceReplacementDifficultyIsTrue : strongArchivesCanReduceReplacementDifficulty ≡ true
    lowResilienceImpliesTargeting : Bool
    lowResilienceImpliesTargetingIsFalse : lowResilienceImpliesTargeting ≡ false

canonicalResilienceBoundary : ResilienceBoundary
canonicalResilienceBoundary = resilience-boundary false refl false refl true refl false refl
