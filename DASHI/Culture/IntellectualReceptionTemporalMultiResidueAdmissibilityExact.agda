module DASHI.Culture.IntellectualReceptionTemporalMultiResidueAdmissibilityExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / TEMPORAL MULTI-RESIDUE ADMISSIBILITY
--
-- The residue ledger is history-indexed and evolves over time.  A final ledger
-- is only the terminal projection of a temporal accumulation R_h(t).
--
-- This module also proves that two histories can share the same final ledger
-- while differing in the time at which a residue was acquired, and therefore
-- differing in intermediate admissibility.  The finite construction is DASHI-
-- owned and is not an empirical claim about an actual intellectual history.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.TrajectoryResidueExact as Residue
import DASHI.Culture.IntellectualReceptionMultiResidueAdmissibilityLedgerExact as Ledger

------------------------------------------------------------------------
-- 1. Finite temporal index and history families.
------------------------------------------------------------------------

data ReceptionTime : Set where
  t0 t1 t2 t3 : ReceptionTime

data TemporalReceptionHistory : Set where
  closureTemporalHistory
  archiveTemporalHistory
  movementEarlyAuthorityHistory
  movementLateAuthorityHistory
  : TemporalReceptionHistory

archiveOnlyLedger : Ledger.ReceptionResidueLedger
archiveOnlyLedger =
  Ledger.reception-residue-ledger
    Residue.residueAbsent Residue.residuePresent Residue.residueAbsent
    Residue.residueAbsent Residue.residueAbsent

movementOnlyLedger : Ledger.ReceptionResidueLedger
movementOnlyLedger =
  Ledger.reception-residue-ledger
    Residue.residueAbsent Residue.residueAbsent Residue.residuePresent
    Residue.residueAbsent Residue.residueAbsent

------------------------------------------------------------------------
-- 2. The primary temporal object: R_h(t).
------------------------------------------------------------------------

ledgerAt :
  TemporalReceptionHistory →
  ReceptionTime →
  Ledger.ReceptionResidueLedger

ledgerAt closureTemporalHistory t0 = Ledger.emptyLedger
ledgerAt closureTemporalHistory t1 = Ledger.closureLedger
ledgerAt closureTemporalHistory t2 = Ledger.closureLedger
ledgerAt closureTemporalHistory t3 = Ledger.closureLedger

ledgerAt archiveTemporalHistory t0 = Ledger.emptyLedger
ledgerAt archiveTemporalHistory t1 = archiveOnlyLedger
ledgerAt archiveTemporalHistory t2 = Ledger.archivePluralLedger
ledgerAt archiveTemporalHistory t3 = Ledger.archivePluralLedger

ledgerAt movementEarlyAuthorityHistory t0 = Ledger.emptyLedger
ledgerAt movementEarlyAuthorityHistory t1 = Ledger.movementAuthorityLedger
ledgerAt movementEarlyAuthorityHistory t2 = Ledger.movementAuthorityLedger
ledgerAt movementEarlyAuthorityHistory t3 = Ledger.movementAuthorityLedger

ledgerAt movementLateAuthorityHistory t0 = Ledger.emptyLedger
ledgerAt movementLateAuthorityHistory t1 = movementOnlyLedger
ledgerAt movementLateAuthorityHistory t2 = Ledger.movementAuthorityLedger
ledgerAt movementLateAuthorityHistory t3 = Ledger.movementAuthorityLedger

finalLedger : TemporalReceptionHistory → Ledger.ReceptionResidueLedger
finalLedger history = ledgerAt history t3

------------------------------------------------------------------------
-- 3. Same final residue vector can hide different deposition timing.
------------------------------------------------------------------------

earlyAndLateAuthorityShareFinalLedger :
  finalLedger movementEarlyAuthorityHistory
  ≡ finalLedger movementLateAuthorityHistory
earlyAndLateAuthorityShareFinalLedger = refl

intermediateAuthorityDiffers :
  Ledger.institutionalAuthorityAcquired
    (ledgerAt movementEarlyAuthorityHistory t1)
  ≡ Ledger.institutionalAuthorityAcquired
    (ledgerAt movementLateAuthorityHistory t1) → ⊥
intermediateAuthorityDiffers ()

------------------------------------------------------------------------
-- 4. Admissibility is evaluated from the ledger at that time.
------------------------------------------------------------------------

data TemporalContinuationMove : Set where
  pluralContinuation movementContinuation authorityContinuation
  : TemporalContinuationMove

enabledByLedger :
  TemporalContinuationMove →
  Ledger.ReceptionResidueLedger →
  Bool

enabledByLedger pluralContinuation state
  with Ledger.archiveRecoveryVisited state | Ledger.pluralSelectionVisited state
... | Residue.residuePresent | Residue.residuePresent = true
... | _ | _ = false

enabledByLedger movementContinuation state
  with Ledger.movementUptakeVisited state
... | Residue.residuePresent = true
... | Residue.residueAbsent = false

enabledByLedger authorityContinuation state
  with Ledger.institutionalAuthorityAcquired state
... | Residue.residuePresent = true
... | Residue.residueAbsent = false

enabledAt :
  TemporalReceptionHistory →
  ReceptionTime →
  TemporalContinuationMove →
  Bool
enabledAt history time move = enabledByLedger move (ledgerAt history time)

earlyAuthorityEnabledAtT1 :
  enabledAt movementEarlyAuthorityHistory t1 authorityContinuation ≡ true
earlyAuthorityEnabledAtT1 = refl

lateAuthorityBlockedAtT1 :
  enabledAt movementLateAuthorityHistory t1 authorityContinuation ≡ false
lateAuthorityBlockedAtT1 = refl

lateAuthorityEnabledAtT2 :
  enabledAt movementLateAuthorityHistory t2 authorityContinuation ≡ true
lateAuthorityEnabledAtT2 = refl

archivePluralBlockedBeforePluralExposure :
  enabledAt archiveTemporalHistory t1 pluralContinuation ≡ false
archivePluralBlockedBeforePluralExposure = refl

archivePluralEnabledAfterPluralExposure :
  enabledAt archiveTemporalHistory t2 pluralContinuation ≡ true
archivePluralEnabledAfterPluralExposure = refl

------------------------------------------------------------------------
-- 5. A terminal snapshot cannot recover temporal acquisition history.
------------------------------------------------------------------------

data AuthorityTimingCase : Set where
  authorityEarly authorityLate : AuthorityTimingCase

data SameFinalLedgerCode : Set where sameMovementAuthorityFinal : SameFinalLedgerCode

data AuthorityAcquisitionTimeCode : Set where acquiredAtT1 acquiredAtT2 : AuthorityAcquisitionTimeCode

finalLedgerCode : AuthorityTimingCase → SameFinalLedgerCode
finalLedgerCode _ = sameMovementAuthorityFinal

authorityAcquisitionTime : AuthorityTimingCase → AuthorityAcquisitionTimeCode
authorityAcquisitionTime authorityEarly = acquiredAtT1
authorityAcquisitionTime authorityLate = acquiredAtT2

authorityAcquisitionTimesDiffer :
  authorityAcquisitionTime authorityEarly
  ≡ authorityAcquisitionTime authorityLate → ⊥
authorityAcquisitionTimesDiffer ()

sameFinalLedgerCannotRecoverAcquisitionTiming :
  INF.FactorsThrough finalLedgerCode authorityAcquisitionTime → ⊥
sameFinalLedgerCannotRecoverAcquisitionTiming =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      authorityEarly authorityLate refl authorityAcquisitionTimesDiffer)

------------------------------------------------------------------------
-- 6. Same final ledger does not recover intermediate admissibility.
------------------------------------------------------------------------

data IntermediateAuthorityProfile : Set where
  authorityAlreadyEnabled authorityNotYetEnabled : IntermediateAuthorityProfile

intermediateAuthorityProfile : AuthorityTimingCase → IntermediateAuthorityProfile
intermediateAuthorityProfile authorityEarly = authorityAlreadyEnabled
intermediateAuthorityProfile authorityLate = authorityNotYetEnabled

intermediateAuthorityProfilesDiffer :
  intermediateAuthorityProfile authorityEarly
  ≡ intermediateAuthorityProfile authorityLate → ⊥
intermediateAuthorityProfilesDiffer ()

sameFinalLedgerCannotRecoverIntermediateAdmissibility :
  INF.FactorsThrough finalLedgerCode intermediateAuthorityProfile → ⊥
sameFinalLedgerCannotRecoverIntermediateAdmissibility =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      authorityEarly authorityLate refl intermediateAuthorityProfilesDiffer)

------------------------------------------------------------------------
-- 7. Temporal points and canonical no-erasure reuse.
------------------------------------------------------------------------

data TemporalPoint : Set where
  earlyT0 earlyT1 earlyT2 earlyT3
  lateT0 lateT1 lateT2 lateT3
  : TemporalPoint

pointLedger : TemporalPoint → Ledger.ReceptionResidueLedger
pointLedger earlyT0 = ledgerAt movementEarlyAuthorityHistory t0
pointLedger earlyT1 = ledgerAt movementEarlyAuthorityHistory t1
pointLedger earlyT2 = ledgerAt movementEarlyAuthorityHistory t2
pointLedger earlyT3 = ledgerAt movementEarlyAuthorityHistory t3
pointLedger lateT0 = ledgerAt movementLateAuthorityHistory t0
pointLedger lateT1 = ledgerAt movementLateAuthorityHistory t1
pointLedger lateT2 = ledgerAt movementLateAuthorityHistory t2
pointLedger lateT3 = ledgerAt movementLateAuthorityHistory t3

data TemporalStep : TemporalPoint → TemporalPoint → Set where
  early01 : TemporalStep earlyT0 earlyT1
  early12 : TemporalStep earlyT1 earlyT2
  early23 : TemporalStep earlyT2 earlyT3
  late01 : TemporalStep lateT0 lateT1
  late12 : TemporalStep lateT1 lateT2
  late23 : TemporalStep lateT2 lateT3

authorityFlag : TemporalPoint → Residue.ResidueFlag
authorityFlag point = Ledger.institutionalAuthorityAcquired (pointLedger point)

noAuthorityErasure : Residue.NoResidueErasure TemporalStep authorityFlag
noAuthorityErasure early01 ()
noAuthorityErasure early12 present = refl
noAuthorityErasure early23 present = refl
noAuthorityErasure late01 ()
noAuthorityErasure late12 ()
noAuthorityErasure late23 present = refl

earlyAuthorityTrace : Residue.Trace TemporalStep earlyT1 earlyT3
earlyAuthorityTrace =
  Residue.traceStep early12
    (Residue.traceStep early23 Residue.traceRefl)

lateAuthorityTrace : Residue.Trace TemporalStep lateT2 lateT3
lateAuthorityTrace =
  Residue.traceStep late23 Residue.traceRefl

earlyAuthorityPersists : authorityFlag earlyT3 ≡ Residue.residuePresent
earlyAuthorityPersists =
  Residue.tracePreservesPresentResidue noAuthorityErasure earlyAuthorityTrace refl

lateAuthorityPersistsAfterAcquisition :
  authorityFlag lateT3 ≡ Residue.residuePresent
lateAuthorityPersistsAfterAcquisition =
  Residue.tracePreservesPresentResidue noAuthorityErasure lateAuthorityTrace refl

------------------------------------------------------------------------
-- 8. Temporal accumulation is finer than terminal state.
------------------------------------------------------------------------

data TemporalTrajectoryCode : Set where
  authorityEarlyTrajectory authorityLateTrajectory : TemporalTrajectoryCode

temporalTrajectoryCode : AuthorityTimingCase → TemporalTrajectoryCode
temporalTrajectoryCode authorityEarly = authorityEarlyTrajectory
temporalTrajectoryCode authorityLate = authorityLateTrajectory

temporalTrajectoriesDiffer :
  temporalTrajectoryCode authorityEarly
  ≡ temporalTrajectoryCode authorityLate → ⊥
temporalTrajectoriesDiffer ()

sameTerminalLedgerCannotRecoverTemporalTrajectory :
  INF.FactorsThrough finalLedgerCode temporalTrajectoryCode → ⊥
sameTerminalLedgerCannotRecoverTemporalTrajectory =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      authorityEarly authorityLate refl temporalTrajectoriesDiffer)

------------------------------------------------------------------------
-- 9. No-promotion boundaries.
------------------------------------------------------------------------

data TemporalLedgerPromotesActualChronology : Set where
data TemporalIndexPromotesPhysicalTime : Set where
data SameFinalLedgerPromotesSameHistory : Set where
data EarlierAdmissibilityPromotesHistoricalPriority : Set where

temporalLedgerDoesNotPromoteActualChronology :
  TemporalLedgerPromotesActualChronology → ⊥
temporalLedgerDoesNotPromoteActualChronology ()

temporalIndexDoesNotPromotePhysicalTime : TemporalIndexPromotesPhysicalTime → ⊥
temporalIndexDoesNotPromotePhysicalTime ()

sameFinalLedgerDoesNotPromoteSameHistory : SameFinalLedgerPromotesSameHistory → ⊥
sameFinalLedgerDoesNotPromoteSameHistory ()

earlierAdmissibilityDoesNotPromoteHistoricalPriority :
  EarlierAdmissibilityPromotesHistoricalPriority → ⊥
earlierAdmissibilityDoesNotPromoteHistoricalPriority ()

------------------------------------------------------------------------
-- 10. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionTemporalMultiResidueBoundary : Set where
  constructor intellectual-reception-temporal-multi-residue-boundary
  field
    residueLedgerIsHistoryIndexedOverTime : Bool
    finalLedgerIsOnlyTerminalProjection : Bool
    sameFinalLedgerDeterminesDepositionTiming : Bool
    sameFinalLedgerDeterminesIntermediateAdmissibility : Bool
    admissibilityCanChangeAsResiduesAccumulate : Bool
    acquiredResidueCanPersistForward : Bool
    temporalIndexIsPhysicalTime : Bool
    temporalFixtureIsActualChronology : Bool
    sourceAttributionBoundarySurvivesTemporalReasoning : Bool

canonicalIntellectualReceptionTemporalMultiResidueBoundary :
  IntellectualReceptionTemporalMultiResidueBoundary
canonicalIntellectualReceptionTemporalMultiResidueBoundary =
  intellectual-reception-temporal-multi-residue-boundary
    true true false false true true false false true
