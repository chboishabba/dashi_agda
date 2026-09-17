module DASHI.Education.DigitalESDSituatedAuditObserverExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Education.DigitalESDSourceAuditScaleExact as Scale

------------------------------------------------------------------------
-- SITUATED AUDIT OBSERVERS
------------------------------------------------------------------------

data ObserverPosition : Set where
  learnerParticipant : ObserverPosition
  disabledAccessNeedsParticipant : ObserverPosition
  teacherSupportWorker : ObserverPosition
  familyCarer : ObserverPosition
  institution : ObserverPosition
  community : ObserverPosition
  workerSupplyChainParticipant : ObserverPosition
  environmentalMaterialObserver : ObserverPosition
  politicalEconomyObserver : ObserverPosition
  technicalSecurityPrivacyObserver : ObserverPosition
  normativeStandardsProcessObserver : ObserverPosition
  researcherModelObserver : ObserverPosition

record SituatedAuditObservation : Set where
  constructor situated-audit-observation
  field
    source : Attr.AttributedSource
    observerPosition : ObserverPosition
    consumerQuestion : String
    axis : Scale.CoreAuditAxis
    evidenceCarrier : String
    score : Scale.Score0to5
    scoreReason : String
    supportingLocator : String
    limitation : String
    context : String
    time : String
    claimCeilingReading : String

open SituatedAuditObservation public

------------------------------------------------------------------------
-- Constructive collision: an institutional availability surface cannot recover
-- situated participant/access state.
------------------------------------------------------------------------

data AuditWorld : Set where
  institutionAvailableAccessible : AuditWorld
  institutionAvailableAccessBroken : AuditWorld

data InstitutionalSurface : Set where institutionReportsAvailable : InstitutionalSurface

data SituatedParticipantState : Set where
  participantCanEffectivelyUse : SituatedParticipantState
  participantCannotEffectivelyUse : SituatedParticipantState

institutionalSurface : AuditWorld → InstitutionalSurface
institutionalSurface institutionAvailableAccessible = institutionReportsAvailable
institutionalSurface institutionAvailableAccessBroken = institutionReportsAvailable

situatedParticipantState : AuditWorld → SituatedParticipantState
situatedParticipantState institutionAvailableAccessible = participantCanEffectivelyUse
situatedParticipantState institutionAvailableAccessBroken = participantCannotEffectivelyUse

participantStatesDiffer :
  situatedParticipantState institutionAvailableAccessible ≡
  situatedParticipantState institutionAvailableAccessBroken → ⊥
participantStatesDiffer ()

institutionalSurfaceParticipantWitness :
  INF.NonFactorabilityWitness institutionalSurface situatedParticipantState
institutionalSurfaceParticipantWitness =
  INF.nonFactorabilityWitness
    institutionAvailableAccessible
    institutionAvailableAccessBroken
    refl
    participantStatesDiffer

institutionalSurfaceCannotDetermineSituatedParticipantState :
  INF.FactorsThrough institutionalSurface situatedParticipantState → ⊥
institutionalSurfaceCannotDetermineSituatedParticipantState =
  INF.witnessRulesOutEveryFlatFactorisation institutionalSurfaceParticipantWitness

data InstitutionalSurfaceDeterminesSituatedParticipantState : Set where

institutionalSurfaceDoesNotDetermineSituatedParticipantState :
  InstitutionalSurfaceDeterminesSituatedParticipantState → ⊥
institutionalSurfaceDoesNotDetermineSituatedParticipantState ()

record SituatedObserverBoundary : Set where
  constructor situated-observer-boundary
  field
    observersAreRanked : Bool
    observersAreRankedIsFalse : observersAreRanked ≡ false
    institutionalSurfaceEqualsParticipantExperience : Bool
    institutionalSurfaceEqualsParticipantExperienceIsFalse :
      institutionalSurfaceEqualsParticipantExperience ≡ false
    oneObserverIsWholeSystem : Bool
    oneObserverIsWholeSystemIsFalse : oneObserverIsWholeSystem ≡ false

open SituatedObserverBoundary public

canonicalSituatedObserverBoundary : SituatedObserverBoundary
canonicalSituatedObserverBoundary = situated-observer-boundary
  false refl
  false refl
  false refl
