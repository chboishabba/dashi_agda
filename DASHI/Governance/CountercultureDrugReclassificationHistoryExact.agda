module DASHI.Governance.CountercultureDrugReclassificationHistoryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.HistoryConditionedChoiceExact as HistoryChoice
import DASHI.Core.TrajectoryResidueExact as Trajectory
import DASHI.Governance.WarOnDrugsHistoricalGenealogyExact as Genealogy
import DASHI.Governance.TrumpDrugPolicyPsychedelicClassificationBidiExact as TrumpPolicy

------------------------------------------------------------------------
-- COUNTERCULTURE -> MEDICAL/VETERAN RECLASSIFICATION HISTORY
--
-- The broad psychoactive/psychedelic domain may be observed similarly while its
-- institutional route changes across history.  Earlier countercultural stigma,
-- criminalisation and political association remain historical residue even when
-- a later institution reclassifies a related substance/use as therapeutic.
------------------------------------------------------------------------

data ReclassificationState : Set where
  countercultureAssociatedState
  punitiveProhibitionState
  researchReopeningState
  veteranTherapeuticState
  commercialTherapeuticState
  : ReclassificationState

data ReclassificationStep : ReclassificationState → ReclassificationState → Set where
  countercultureToPunitive :
    ReclassificationStep countercultureAssociatedState punitiveProhibitionState
  punitiveToResearchReopening :
    ReclassificationStep punitiveProhibitionState researchReopeningState
  researchToVeteranTherapeutic :
    ReclassificationStep researchReopeningState veteranTherapeuticState
  researchToCommercialTherapeutic :
    ReclassificationStep researchReopeningState commercialTherapeuticState

history : ReclassificationState → ReclassificationState → Set
history = Trajectory.Trace ReclassificationStep

countercultureToVeteranHistory :
  history countercultureAssociatedState veteranTherapeuticState
countercultureToVeteranHistory =
  Trajectory.traceStep countercultureToPunitive
    (Trajectory.traceStep punitiveToResearchReopening
      (Trajectory.traceStep researchToVeteranTherapeutic Trajectory.traceRefl))

countercultureToCommercialHistory :
  history countercultureAssociatedState commercialTherapeuticState
countercultureToCommercialHistory =
  Trajectory.traceStep countercultureToPunitive
    (Trajectory.traceStep punitiveToResearchReopening
      (Trajectory.traceStep researchToCommercialTherapeutic Trajectory.traceRefl))

------------------------------------------------------------------------
-- Coarse observer sees only present therapeutic legitimacy.
------------------------------------------------------------------------

data PresentLegibility : Set where
  countercultureLegibility
  prohibitedLegibility
  therapeuticLegibility
  : PresentLegibility

observePresent : ReclassificationState → PresentLegibility
observePresent countercultureAssociatedState = countercultureLegibility
observePresent punitiveProhibitionState = prohibitedLegibility
observePresent researchReopeningState = therapeuticLegibility
observePresent veteranTherapeuticState = therapeuticLegibility
observePresent commercialTherapeuticState = therapeuticLegibility

veteranCommercialPresentCollision :
  observePresent veteranTherapeuticState ≡ observePresent commercialTherapeuticState
veteranCommercialPresentCollision = refl

------------------------------------------------------------------------
-- Historical residue distinguishes routes despite present therapeutic collision.
------------------------------------------------------------------------

data RouteResidue : Set where
  criminalizationResidue
  countercultureStigmaResidue
  veteranInstitutionalPrivilegeResidue
  commercialExtractionResidue
  : RouteResidue

record ReclassificationHistoryReceipt : Set where
  constructor reclassificationHistoryReceipt
  field
    arrival : ReclassificationState
    priorCriminalizationRetained : Bool
    priorCountercultureAssociationRetained : Bool
    routeSpecificResidue : RouteResidue
    historyReference : String

open ReclassificationHistoryReceipt public

veteranHistoryReceipt : ReclassificationHistoryReceipt
veteranHistoryReceipt = reclassificationHistoryReceipt
  veteranTherapeuticState
  true
  true
  veteranInstitutionalPrivilegeResidue
  "counterculture association -> punitive prohibition -> research reopening -> veteran therapeutic route"

commercialHistoryReceipt : ReclassificationHistoryReceipt
commercialHistoryReceipt = reclassificationHistoryReceipt
  commercialTherapeuticState
  true
  true
  commercialExtractionResidue
  "counterculture association -> punitive prohibition -> research reopening -> commercial therapeutic route"

------------------------------------------------------------------------
-- Same present therapeutic classification does not recover historical route.
------------------------------------------------------------------------

data PresentTherapeuticPromotesSameHistory : Set where

data TherapeuticReclassificationErasesCriminalizationHistory : Set where

data MedicalLegitimacyPromotesCountercultureError : Set where

presentTherapeuticDoesNotPromoteSameHistory :
  PresentTherapeuticPromotesSameHistory → ⊥
presentTherapeuticDoesNotPromoteSameHistory ()

reclassificationDoesNotEraseCriminalizationHistory :
  TherapeuticReclassificationErasesCriminalizationHistory → ⊥
reclassificationDoesNotEraseCriminalizationHistory ()

medicalLegitimacyDoesNotPromoteCountercultureError :
  MedicalLegitimacyPromotesCountercultureError → ⊥
medicalLegitimacyDoesNotPromoteCountercultureError ()

genealogyBoundary : Genealogy.WarOnDrugsHistoricalGenealogyBoundary
genealogyBoundary = Genealogy.canonicalWarOnDrugsHistoricalGenealogyBoundary

trumpBoundary : TrumpPolicy.TrumpDrugPolicyClassificationBoundary
trumpBoundary = TrumpPolicy.canonicalTrumpDrugPolicyClassificationBoundary

record CountercultureDrugReclassificationBoundary : Set where
  constructor countercultureDrugReclassificationBoundary
  field
    therapeuticReclassificationCanFollowPunitiveHistory : Bool
    therapeuticReclassificationCanFollowPunitiveHistoryIsTrue :
      therapeuticReclassificationCanFollowPunitiveHistory ≡ true
    samePresentTherapeuticLegibilityImpliesSameHistory : Bool
    samePresentTherapeuticLegibilityImpliesSameHistoryIsFalse :
      samePresentTherapeuticLegibilityImpliesSameHistory ≡ false
    laterMedicalRecognitionErasesCountercultureHistory : Bool
    laterMedicalRecognitionErasesCountercultureHistoryIsFalse :
      laterMedicalRecognitionErasesCountercultureHistory ≡ false
    historicalStigmaAndLaterTherapeuticValueCanCoexist : Bool
    historicalStigmaAndLaterTherapeuticValueCanCoexistIsTrue :
      historicalStigmaAndLaterTherapeuticValueCanCoexist ≡ true

canonicalCountercultureDrugReclassificationBoundary :
  CountercultureDrugReclassificationBoundary
canonicalCountercultureDrugReclassificationBoundary =
  countercultureDrugReclassificationBoundary
    true refl
    false refl
    false refl
    true refl
