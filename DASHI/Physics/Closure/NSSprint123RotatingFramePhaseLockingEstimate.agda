module DASHI.Physics.Closure.NSSprint123RotatingFramePhaseLockingEstimate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSSprint122NonCircularRotatingStrainPersistenceBound
  as Sprint122

------------------------------------------------------------------------
-- Sprint 123 rotating-frame phase-locking-estimate receipt.
--
-- Sprint122 is imported as the non-circular persistence obstruction.  This
-- Sprint123 receipt records the next fail-closed gate: a phase-locking
-- estimate may not be imposed by hand.  It must be derived from the
-- Navier-Stokes rotating-frame dynamics, must keep the damping/drift balance
-- favorable for a positive dwell window, and must still leave the rotating
-- strain flux budget and Clay assembly gates open.

sprint123RotatingFramePhaseLockingLedgerClosed : Bool
sprint123RotatingFramePhaseLockingLedgerClosed = true

sprint122PersistenceImported : Bool
sprint122PersistenceImported = true

rotatingFramePhaseLockingEstimateRecorded : Bool
rotatingFramePhaseLockingEstimateRecorded = true

nseDerivedPhaseODERequirementRecorded : Bool
nseDerivedPhaseODERequirementRecorded = true

dampingDriftBalanceRecorded : Bool
dampingDriftBalanceRecorded = true

favorableWindowLowerBoundRequirementRecorded : Bool
favorableWindowLowerBoundRequirementRecorded = true

classifierSamplerRecorded : Bool
classifierSamplerRecorded = true

imposedLockingRejected : Bool
imposedLockingRejected = true

rotatingFramePhaseLockingEstimateClosed : Bool
rotatingFramePhaseLockingEstimateClosed = false

favorablePhaseLagWindowLowerBoundClosed : Bool
favorablePhaseLagWindowLowerBoundClosed = false

rotatingStrainFluxBudgetBeatsKStarClosed : Bool
rotatingStrainFluxBudgetBeatsKStarClosed = false

kStarCollapseFromRotatingStrainClosed : Bool
kStarCollapseFromRotatingStrainClosed = false

blowupCriterionBridgeClosed : Bool
blowupCriterionBridgeClosed = false

globalLerayCompatibleRotatingStrainDataClosed : Bool
globalLerayCompatibleRotatingStrainDataClosed = false

navierStokesClayAssemblyClosed : Bool
navierStokesClayAssemblyClosed = false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

record ImportedSprint122Persistence : Set where
  constructor importedSprint122PersistenceReceipt
  field
    sprint122Receipt :
      Sprint122.NSSprint122NonCircularRotatingStrainPersistenceBound
    sprint122ReceiptIsCanonical :
      sprint122Receipt
      ≡ Sprint122.canonicalNSSprint122NonCircularRotatingStrainPersistenceBound
    sprint122LedgerClosed :
      Sprint122.sprint122NonCircularRotatingStrainPersistenceLedgerClosed ≡ true
    sprint122ImportedField :
      sprint122PersistenceImported ≡ true
    sprint122PersistenceStillOpen :
      Sprint122.nonCircularRotatingStrainPersistenceBoundClosed ≡ false
    sprint122RotatingBudgetStillOpen :
      Sprint122.rotatingStrainFluxBudgetBeatsKStarClosed ≡ false
    sprint122KStarCollapseStillOpen :
      Sprint122.kStarCollapseFromRotatingStrainClosed ≡ false
    sprint122BlowupBridgeStillOpen :
      Sprint122.blowupCriterionBridgeClosed ≡ false
    sprint122GlobalDataStillOpen :
      Sprint122.globalLerayCompatibleRotatingStrainDataClosed ≡ false
    sprint122ClayAssemblyStillOpen :
      Sprint122.navierStokesClayAssemblyClosed ≡ false
    sprint122ClayPromotionStillFalse :
      Sprint122.clayNavierStokesPromoted ≡ false
    importedStatus :
      String
    importedStatusIsRequested :
      importedStatus ≡ "Sprint123 imports Sprint122 persistence obstruction"

open ImportedSprint122Persistence public

canonicalImportedSprint122Persistence : ImportedSprint122Persistence
canonicalImportedSprint122Persistence =
  importedSprint122PersistenceReceipt
    Sprint122.canonicalNSSprint122NonCircularRotatingStrainPersistenceBound
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    "Sprint123 imports Sprint122 persistence obstruction"
    refl

record RotatingFramePhaseLockingEstimateReceipt : Set where
  constructor rotatingFramePhaseLockingEstimateReceipt
  field
    receiptName :
      String
    receiptNameIsRequested :
      receiptName ≡ "RotatingFramePhaseLockingEstimate"
    estimateStatus :
      String
    estimateStatusIsRequested :
      estimateStatus ≡ "phase locking must follow from NSE-derived frame dynamics"
    rotatingFramePhaseLockingEstimateRecordedField :
      rotatingFramePhaseLockingEstimateRecorded ≡ true
    rotatingFramePhaseLockingEstimateClosedField :
      rotatingFramePhaseLockingEstimateClosed ≡ false

open RotatingFramePhaseLockingEstimateReceipt public

canonicalRotatingFramePhaseLockingEstimateReceipt :
  RotatingFramePhaseLockingEstimateReceipt
canonicalRotatingFramePhaseLockingEstimateReceipt =
  rotatingFramePhaseLockingEstimateReceipt
    "RotatingFramePhaseLockingEstimate"
    refl
    "phase locking must follow from NSE-derived frame dynamics"
    refl
    refl
    refl

record NSEDerivedPhaseODERequirement : Set where
  constructor nseDerivedPhaseODERequirementReceipt
  field
    requirementStatement :
      String
    requirementStatementIsRequested :
      requirementStatement
      ≡ "phase locking must follow from NSE-derived frame dynamics"
    sourceObstruction :
      String
    sourceObstructionIsRequested :
      sourceObstruction ≡ "imposed phase locking is circular"
    nseDerivedPhaseODERequirementRecordedField :
      nseDerivedPhaseODERequirementRecorded ≡ true

open NSEDerivedPhaseODERequirement public

canonicalNSEDerivedPhaseODERequirement :
  NSEDerivedPhaseODERequirement
canonicalNSEDerivedPhaseODERequirement =
  nseDerivedPhaseODERequirementReceipt
    "phase locking must follow from NSE-derived frame dynamics"
    refl
    "imposed phase locking is circular"
    refl
    refl

record DampingDriftBalance : Set where
  constructor dampingDriftBalanceReceipt
  field
    balanceStatement :
      String
    balanceStatementIsRequested :
      balanceStatement
      ≡ "damping drift and strain rotation must leave positive dwell time"
    windowRequirement :
      String
    windowRequirementIsRequested :
      windowRequirement ≡ "requires favorable phase-lag window lower bound"
    dampingDriftBalanceRecordedField :
      dampingDriftBalanceRecorded ≡ true

open DampingDriftBalance public

canonicalDampingDriftBalance : DampingDriftBalance
canonicalDampingDriftBalance =
  dampingDriftBalanceReceipt
    "damping drift and strain rotation must leave positive dwell time"
    refl
    "requires favorable phase-lag window lower bound"
    refl
    refl

record FavorableWindowLowerBoundRequirement : Set where
  constructor favorableWindowLowerBoundRequirementReceipt
  field
    lowerBoundRequirement :
      String
    lowerBoundRequirementIsRequested :
      lowerBoundRequirement ≡ "requires favorable phase-lag window lower bound"
    dwellTimeCondition :
      String
    dwellTimeConditionIsRequested :
      dwellTimeCondition
      ≡ "damping drift and strain rotation must leave positive dwell time"
    favorableWindowLowerBoundRequirementRecordedField :
      favorableWindowLowerBoundRequirementRecorded ≡ true
    favorablePhaseLagWindowLowerBoundClosedField :
      favorablePhaseLagWindowLowerBoundClosed ≡ false

open FavorableWindowLowerBoundRequirement public

canonicalFavorableWindowLowerBoundRequirement :
  FavorableWindowLowerBoundRequirement
canonicalFavorableWindowLowerBoundRequirement =
  favorableWindowLowerBoundRequirementReceipt
    "requires favorable phase-lag window lower bound"
    refl
    "damping drift and strain rotation must leave positive dwell time"
    refl
    refl
    refl

record ClassifierSamplerReceipt : Set where
  constructor classifierSamplerReceipt
  field
    classifierSamplerRecordedField :
      classifierSamplerRecorded ≡ true
    candidateLemma :
      String
    candidateLemmaIsRequested :
      candidateLemma ≡ "RotatingFramePhaseLockingEstimate"
    requiredDynamics :
      String
    requiredDynamicsIsRequested :
      requiredDynamics
      ≡ "phase locking must follow from NSE-derived frame dynamics"
    requiredWindow :
      String
    requiredWindowIsRequested :
      requiredWindow ≡ "requires favorable phase-lag window lower bound"
    openBudget :
      String
    openBudgetIsRequested :
      openBudget ≡ "RotatingStrainFluxBudgetBeatsKStar remains open"
    recommendedNextLemma :
      String
    recommendedNextLemmaIsRequested :
      recommendedNextLemma ≡ "FavorablePhaseLagWindowLowerBound"
    completionStatus :
      String
    completionStatusIsRequested :
      completionStatus ≡ "complete=false"
    clayStatus :
      String
    clayStatusIsRequested :
      clayStatus ≡ "clay=false"

open ClassifierSamplerReceipt public

canonicalClassifierSamplerReceipt : ClassifierSamplerReceipt
canonicalClassifierSamplerReceipt =
  classifierSamplerReceipt
    refl
    "RotatingFramePhaseLockingEstimate"
    refl
    "phase locking must follow from NSE-derived frame dynamics"
    refl
    "requires favorable phase-lag window lower bound"
    refl
    "RotatingStrainFluxBudgetBeatsKStar remains open"
    refl
    "FavorablePhaseLagWindowLowerBound"
    refl
    "complete=false"
    refl
    "clay=false"
    refl

record ImposedLockingRejection : Set where
  constructor imposedLockingRejectionReceipt
  field
    rejectionStatement :
      String
    rejectionStatementIsRequested :
      rejectionStatement ≡ "imposed phase locking is circular"
    correction :
      String
    correctionIsRequested :
      correction ≡ "phase locking must follow from NSE-derived frame dynamics"
    imposedLockingRejectedField :
      imposedLockingRejected ≡ true

open ImposedLockingRejection public

canonicalImposedLockingRejection : ImposedLockingRejection
canonicalImposedLockingRejection =
  imposedLockingRejectionReceipt
    "imposed phase locking is circular"
    refl
    "phase locking must follow from NSE-derived frame dynamics"
    refl
    refl

record Sprint123GateStatuses : Set where
  constructor sprint123GateStatuses
  field
    sprint123LedgerClosedField :
      sprint123RotatingFramePhaseLockingLedgerClosed ≡ true
    sprint122PersistenceImportedField :
      sprint122PersistenceImported ≡ true
    rotatingFramePhaseLockingEstimateRecordedField :
      rotatingFramePhaseLockingEstimateRecorded ≡ true
    nseDerivedPhaseODERequirementRecordedField :
      nseDerivedPhaseODERequirementRecorded ≡ true
    dampingDriftBalanceRecordedField :
      dampingDriftBalanceRecorded ≡ true
    favorableWindowLowerBoundRequirementRecordedField :
      favorableWindowLowerBoundRequirementRecorded ≡ true
    classifierSamplerRecordedField :
      classifierSamplerRecorded ≡ true
    imposedLockingRejectedField :
      imposedLockingRejected ≡ true
    rotatingFramePhaseLockingEstimateClosedField :
      rotatingFramePhaseLockingEstimateClosed ≡ false
    favorablePhaseLagWindowLowerBoundClosedField :
      favorablePhaseLagWindowLowerBoundClosed ≡ false
    rotatingBudgetClosedField :
      rotatingStrainFluxBudgetBeatsKStarClosed ≡ false
    kStarCollapseClosedField :
      kStarCollapseFromRotatingStrainClosed ≡ false
    blowupCriterionBridgeClosedField :
      blowupCriterionBridgeClosed ≡ false
    globalLerayCompatibleDataClosedField :
      globalLerayCompatibleRotatingStrainDataClosed ≡ false
    navierStokesClayAssemblyClosedField :
      navierStokesClayAssemblyClosed ≡ false
    clayNavierStokesPromotedField :
      clayNavierStokesPromoted ≡ false
    rotatingBudgetOpenStatement :
      String
    rotatingBudgetOpenStatementIsRequested :
      rotatingBudgetOpenStatement
      ≡ "RotatingStrainFluxBudgetBeatsKStar remains open"
    clayPromotionStatement :
      String
    clayPromotionStatementIsRequested :
      clayPromotionStatement ≡ "clayNavierStokesPromoted remains false"

open Sprint123GateStatuses public

canonicalSprint123GateStatuses : Sprint123GateStatuses
canonicalSprint123GateStatuses =
  sprint123GateStatuses
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    "RotatingStrainFluxBudgetBeatsKStar remains open"
    refl
    "clayNavierStokesPromoted remains false"
    refl

record RotatingFramePhaseLockingEstimate : Set where
  constructor rotatingFramePhaseLockingEstimateAggregateReceipt
  field
    importedSprint122 :
      ImportedSprint122Persistence
    estimateReceipt :
      RotatingFramePhaseLockingEstimateReceipt
    nseDerivedPhaseODE :
      NSEDerivedPhaseODERequirement
    dampingDriftBalance :
      DampingDriftBalance
    favorableWindowRequirement :
      FavorableWindowLowerBoundRequirement
    classifierSampler :
      ClassifierSamplerReceipt
    imposedLockingRejection :
      ImposedLockingRejection
    gateStatuses :
      Sprint123GateStatuses
    gateStatusesAreCanonical :
      gateStatuses ≡ canonicalSprint123GateStatuses

open RotatingFramePhaseLockingEstimate public

canonicalRotatingFramePhaseLockingEstimate :
  RotatingFramePhaseLockingEstimate
canonicalRotatingFramePhaseLockingEstimate =
  rotatingFramePhaseLockingEstimateAggregateReceipt
    canonicalImportedSprint122Persistence
    canonicalRotatingFramePhaseLockingEstimateReceipt
    canonicalNSEDerivedPhaseODERequirement
    canonicalDampingDriftBalance
    canonicalFavorableWindowLowerBoundRequirement
    canonicalClassifierSamplerReceipt
    canonicalImposedLockingRejection
    canonicalSprint123GateStatuses
    refl

NSSprint123RotatingFramePhaseLockingEstimate : Set
NSSprint123RotatingFramePhaseLockingEstimate =
  RotatingFramePhaseLockingEstimate

canonicalNSSprint123RotatingFramePhaseLockingEstimate :
  NSSprint123RotatingFramePhaseLockingEstimate
canonicalNSSprint123RotatingFramePhaseLockingEstimate =
  canonicalRotatingFramePhaseLockingEstimate

sprint123ReceiptSummary :
  ImportedSprint122Persistence
  × RotatingFramePhaseLockingEstimateReceipt
  × NSEDerivedPhaseODERequirement
  × DampingDriftBalance
  × FavorableWindowLowerBoundRequirement
  × ClassifierSamplerReceipt
  × ImposedLockingRejection
  × Sprint123GateStatuses
sprint123ReceiptSummary =
  canonicalImportedSprint122Persistence ,
  canonicalRotatingFramePhaseLockingEstimateReceipt ,
  canonicalNSEDerivedPhaseODERequirement ,
  canonicalDampingDriftBalance ,
  canonicalFavorableWindowLowerBoundRequirement ,
  canonicalClassifierSamplerReceipt ,
  canonicalImposedLockingRejection ,
  canonicalSprint123GateStatuses
