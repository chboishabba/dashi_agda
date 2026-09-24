module DASHI.Education.DigitalESDSituatedAuditObserverRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDSituatedAuditObserverExact as Observer

learnerPinned : Observer.ObserverPosition
learnerPinned = Observer.learnerParticipant

disabledLearnerPinned : Observer.ObserverPosition
disabledLearnerPinned = Observer.disabledAccessNeedsParticipant

teacherPinned : Observer.ObserverPosition
teacherPinned = Observer.teacherSupportWorker

familyPinned : Observer.ObserverPosition
familyPinned = Observer.familyCarer

institutionPinned : Observer.ObserverPosition
institutionPinned = Observer.institution

communityPinned : Observer.ObserverPosition
communityPinned = Observer.community

workerPinned : Observer.ObserverPosition
workerPinned = Observer.workerSupplyChainParticipant

environmentPinned : Observer.ObserverPosition
environmentPinned = Observer.environmentalMaterialObserver

politicalEconomyPinned : Observer.ObserverPosition
politicalEconomyPinned = Observer.politicalEconomyObserver

technicalPinned : Observer.ObserverPosition
technicalPinned = Observer.technicalSecurityPrivacyObserver

standardsPinned : Observer.ObserverPosition
standardsPinned = Observer.normativeStandardsProcessObserver

researcherPinned : Observer.ObserverPosition
researcherPinned = Observer.researcherModelObserver

institutionCannotRecoverParticipantState :
  Observer.InstitutionalSurfaceDeterminesSituatedParticipantState → ⊥
institutionCannotRecoverParticipantState =
  Observer.institutionalSurfaceDoesNotDetermineSituatedParticipantState
