module DASHI.Law.SensibLawPersonalProfessionalComparativeWorldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawPersonalWorldProfessionalHandoffExact as Handoff

------------------------------------------------------------------------
-- M11 / S26.5 SAME WORLD, DIFFERENT LEGITIMATE CONSUMER FIBRES
------------------------------------------------------------------------

data Visibility : Set where
  visible : Visibility
  scopeBlocked : Visibility
  notReady : Visibility
  dependencyIrrelevant : Visibility
  unreviewed : Visibility

personalVisibility :
  Handoff.Coordinate → Visibility
personalVisibility coordinate = visible

lawyerVisibility :
  Handoff.Coordinate → Visibility
lawyerVisibility Handoff.reviewedEvent = visible
lawyerVisibility Handoff.reviewedDocument = visible
lawyerVisibility Handoff.reviewedFact = visible
lawyerVisibility Handoff.privateHypothesis = scopeBlocked
lawyerVisibility Handoff.notReadyJournalMaterial = notReady

doctorVisibility :
  Handoff.Coordinate → Visibility
doctorVisibility Handoff.reviewedEvent = visible
doctorVisibility Handoff.reviewedDocument = visible
doctorVisibility Handoff.reviewedFact = visible
doctorVisibility Handoff.privateHypothesis = scopeBlocked
doctorVisibility Handoff.notReadyJournalMaterial = notReady

advocateVisibility :
  Handoff.Coordinate → Visibility
advocateVisibility Handoff.reviewedEvent = visible
advocateVisibility Handoff.reviewedDocument = dependencyIrrelevant
advocateVisibility Handoff.reviewedFact = visible
advocateVisibility Handoff.privateHypothesis = scopeBlocked
advocateVisibility Handoff.notReadyJournalMaterial = notReady

regulatorVisibility :
  Handoff.Coordinate → Visibility
regulatorVisibility Handoff.reviewedEvent = dependencyIrrelevant
regulatorVisibility Handoff.reviewedDocument = visible
regulatorVisibility Handoff.reviewedFact = visible
regulatorVisibility Handoff.privateHypothesis = scopeBlocked
regulatorVisibility Handoff.notReadyJournalMaterial = notReady

personalAndLawyerShareReviewedFact :
  personalVisibility Handoff.reviewedFact
    ≡ lawyerVisibility Handoff.reviewedFact
personalAndLawyerShareReviewedFact = refl

personalAndRegulatorDifferOnEventVisibility :
  personalVisibility Handoff.reviewedEvent
    ≡ regulatorVisibility Handoff.reviewedEvent → ⊥
personalAndRegulatorDifferOnEventVisibility ()

privateHypothesisDifferenceIsScopeTyped :
  lawyerVisibility Handoff.privateHypothesis ≡ scopeBlocked
privateHypothesisDifferenceIsScopeTyped = refl

notReadyDifferenceIsReadinessTyped :
  doctorVisibility Handoff.notReadyJournalMaterial ≡ notReady
notReadyDifferenceIsReadinessTyped = refl

data DifferentFibreMeansDifferentCanonicalWorld : Set where
data ScopeBlockedMeansFalse : Set where
data DependencyIrrelevantMeansDeleted : Set where
data PersonalProjectionIsTruerThanProfessional : Set where
data ProfessionalProjectionIsTruerThanPersonal : Set where

differentFibreDoesNotCreateSecondWorld :
  DifferentFibreMeansDifferentCanonicalWorld → ⊥
differentFibreDoesNotCreateSecondWorld ()

scopeBlockedDoesNotMeanFalse :
  ScopeBlockedMeansFalse → ⊥
scopeBlockedDoesNotMeanFalse ()

dependencyIrrelevantDoesNotMeanDeleted :
  DependencyIrrelevantMeansDeleted → ⊥
dependencyIrrelevantDoesNotMeanDeleted ()

personalIsNotPromotedToTruerWorld :
  PersonalProjectionIsTruerThanProfessional → ⊥
personalIsNotPromotedToTruerWorld ()

professionalIsNotPromotedToTruerWorld :
  ProfessionalProjectionIsTruerThanPersonal → ⊥
professionalIsNotPromotedToTruerWorld ()

record PersonalProfessionalComparativeBoundary : Set where
  constructor personalProfessionalComparativeBoundary
  field
    sameCanonicalWorld : Bool
    sameCanonicalWorldIsTrue : sameCanonicalWorld ≡ true

    differentLegitimateFibres : Bool
    differentLegitimateFibresIsTrue : differentLegitimateFibres ≡ true

    privateDifferenceExplainedByScope : Bool
    privateDifferenceExplainedByScopeIsTrue :
      privateDifferenceExplainedByScope ≡ true

    notReadyDifferenceExplainedByReadiness : Bool
    notReadyDifferenceExplainedByReadinessIsTrue :
      notReadyDifferenceExplainedByReadiness ≡ true

    dependencyDifferenceExplainedByConsumerSlice : Bool
    dependencyDifferenceExplainedByConsumerSliceIsTrue :
      dependencyDifferenceExplainedByConsumerSlice ≡ true

    eitherProjectionDeclaredTruer : Bool
    eitherProjectionDeclaredTruerIsFalse :
      eitherProjectionDeclaredTruer ≡ false

open PersonalProfessionalComparativeBoundary public

canonicalPersonalProfessionalComparativeBoundary :
  PersonalProfessionalComparativeBoundary
canonicalPersonalProfessionalComparativeBoundary =
  personalProfessionalComparativeBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
