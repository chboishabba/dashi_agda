module DASHI.Governance.DrugCategoryConsumerQuotientRefinementExact where

open import DASHI.Core.Prelude

import DASHI.Governance.DrugCategoryExplicitConsumerQuotientExact as Quotient
import DASHI.Governance.DrugCategoryClinicalQuotientRelativeFibreExact as Relative

------------------------------------------------------------------------
-- CONSUMER-DRIVEN QUOTIENT REFINEMENT
--
-- If a fine consumer does not descend through the clinical quotient, the
-- backward move is not "recover the whole world".  Add only the coordinate
-- needed to separate the declared collision.
------------------------------------------------------------------------

data RefinementCoordinate : Set where
  addSubjectPosition
  addHistoricalPosition
  addSubjectAndHistory
  : RefinementCoordinate

data RefinementDemand : Set where
  subjectConsumerDemand
  historyConsumerDemand
  fullSemanticStateDemand
  : RefinementDemand

requiredRefinement : RefinementDemand → RefinementCoordinate
requiredRefinement subjectConsumerDemand = addSubjectPosition
requiredRefinement historyConsumerDemand = addHistoricalPosition
requiredRefinement fullSemanticStateDemand = addSubjectAndHistory

------------------------------------------------------------------------
-- Refined observers.
------------------------------------------------------------------------

ClinicalSubjectObservation : Set
ClinicalSubjectObservation =
  Quotient.ClinicalObservation × Quotient.SubjectObservation

ClinicalHistoryObservation : Set
ClinicalHistoryObservation =
  Quotient.ClinicalObservation × Quotient.HistoryObservation

clinicalSubjectObserver : Quotient.TranslationState → ClinicalSubjectObservation
clinicalSubjectObserver state =
  Quotient.clinicalObserver state , Quotient.subjectObserver state

clinicalHistoryObserver : Quotient.TranslationState → ClinicalHistoryObservation
clinicalHistoryObserver state =
  Quotient.clinicalObserver state , Quotient.historyObserver state

------------------------------------------------------------------------
-- Minimal declared collision separation.
------------------------------------------------------------------------

clinicalSubjectSeparatesStateFromLived :
  clinicalSubjectObserver Quotient.stateLegalState
  ≡ clinicalSubjectObserver Quotient.livedSubjectState → ⊥
clinicalSubjectSeparatesStateFromLived ()

clinicalHistorySeparatesStateFromBiomedical :
  clinicalHistoryObserver Quotient.stateLegalState
  ≡ clinicalHistoryObserver Quotient.biomedicalState → ⊥
clinicalHistorySeparatesStateFromBiomedical ()

------------------------------------------------------------------------
-- One extra coordinate need not reconstruct every fine distinction.
------------------------------------------------------------------------

clinicalSubjectStillCollapsesStateAndBiomedical :
  clinicalSubjectObserver Quotient.stateLegalState
  ≡ clinicalSubjectObserver Quotient.biomedicalState
clinicalSubjectStillCollapsesStateAndBiomedical = refl

clinicalHistoryStillCollapsesStateAndLived :
  clinicalHistoryObserver Quotient.stateLegalState
  ≡ clinicalHistoryObserver Quotient.livedSubjectState
clinicalHistoryStillCollapsesStateAndLived = refl

------------------------------------------------------------------------
-- The full coarse+relative-fine observer is separating because the canonical
-- coarse/fine owner already proves exact reopening.
------------------------------------------------------------------------

fullRefinedObserver :
  Quotient.TranslationState →
  Quotient.ClinicalObservation × Relative.RelativeSemantic
fullRefinedObserver state =
  Quotient.clinicalObserver state , Relative.relativeSemantic state

fullRefinedObserverSeparating :
  (left right : Quotient.TranslationState) →
  fullRefinedObserver left ≡ fullRefinedObserver right →
  left ≡ right
fullRefinedObserverSeparating =
  Relative.clinicalRelativeObserverSeparating

------------------------------------------------------------------------
-- BIDI backprop from non-descent to the least declared refinement class.
------------------------------------------------------------------------

subjectNonDescentCreatesRefinementDemand :
  (Quotient.DescendsThrough
    Quotient.subjectObserver Quotient.clinicalObserver → ⊥)
  → RefinementCoordinate
subjectNonDescentCreatesRefinementDemand blocked = addSubjectPosition

historyNonDescentCreatesRefinementDemand :
  (Quotient.DescendsThrough
    Quotient.historyObserver Quotient.clinicalObserver → ⊥)
  → RefinementCoordinate
historyNonDescentCreatesRefinementDemand blocked = addHistoricalPosition

canonicalSubjectRefinement : RefinementCoordinate
canonicalSubjectRefinement =
  subjectNonDescentCreatesRefinementDemand
    Quotient.subjectCannotDescendThroughClinical

canonicalHistoryRefinement : RefinementCoordinate
canonicalHistoryRefinement =
  historyNonDescentCreatesRefinementDemand
    Quotient.historyCannotDescendThroughClinical

------------------------------------------------------------------------
-- Hard boundaries.
------------------------------------------------------------------------

data OneProbePromotesFullStateRecovery : Set where

data RefinementDemandPromotesEmpiricalMeasurement : Set where

data FailureToDescendPromotesWholeQuotientInvalidity : Set where

oneProbeDoesNotPromoteFullStateRecovery :
  OneProbePromotesFullStateRecovery → ⊥
oneProbeDoesNotPromoteFullStateRecovery ()

refinementDemandDoesNotPromoteEmpiricalMeasurement :
  RefinementDemandPromotesEmpiricalMeasurement → ⊥
refinementDemandDoesNotPromoteEmpiricalMeasurement ()

failureToDescendDoesNotPromoteWholeQuotientInvalidity :
  FailureToDescendPromotesWholeQuotientInvalidity → ⊥
failureToDescendDoesNotPromoteWholeQuotientInvalidity ()

record DrugCategoryConsumerQuotientRefinementBoundary : Set where
  constructor drugCategoryConsumerQuotientRefinementBoundary
  field
    failedDescentCanGenerateConsumerSpecificRefinement : Bool
    failedDescentCanGenerateConsumerSpecificRefinementIsTrue :
      failedDescentCanGenerateConsumerSpecificRefinement ≡ true
    subjectProbeSeparatesSubjectCollision : Bool
    subjectProbeSeparatesSubjectCollisionIsTrue :
      subjectProbeSeparatesSubjectCollision ≡ true
    historyProbeSeparatesHistoryCollision : Bool
    historyProbeSeparatesHistoryCollisionIsTrue :
      historyProbeSeparatesHistoryCollision ≡ true
    oneProbeAlwaysRecoversWholeFineState : Bool
    oneProbeAlwaysRecoversWholeFineStateIsFalse :
      oneProbeAlwaysRecoversWholeFineState ≡ false
    fullClinicalSubjectHistoryObserverIsSeparating : Bool
    fullClinicalSubjectHistoryObserverIsSeparatingIsTrue :
      fullClinicalSubjectHistoryObserverIsSeparating ≡ true

canonicalDrugCategoryConsumerQuotientRefinementBoundary :
  DrugCategoryConsumerQuotientRefinementBoundary
canonicalDrugCategoryConsumerQuotientRefinementBoundary =
  drugCategoryConsumerQuotientRefinementBoundary
    true refl
    true refl
    true refl
    false refl
    true refl
