module DASHI.Governance.DrugCategoryClinicalQuotientRelativeFibreExact where

open import DASHI.Core.Prelude

import DASHI.Core.CoarseFineRelativeFibreExact as CoarseFine
import DASHI.Governance.DrugCategoryExplicitConsumerQuotientExact as Quotient

------------------------------------------------------------------------
-- CLINICAL QUOTIENT + RELATIVE-FINE SEMANTIC FIBRE
--
-- The clinical observer is a valid coarse quotient for a narrow clinical
-- consumer.  Subject-position and historical position are retained as a
-- relative-fine fibre.  Coarse + relative-fine reconstructs the finite state
-- exactly.
------------------------------------------------------------------------

RelativeSemantic : Set
RelativeSemantic = Quotient.SubjectObservation × Quotient.HistoryObservation

relativeSemantic : Quotient.TranslationState → RelativeSemantic
relativeSemantic state =
  Quotient.subjectObserver state , Quotient.historyObserver state

reopenClinicalRelative :
  Quotient.ClinicalObservation → RelativeSemantic → Quotient.TranslationState
reopenClinicalRelative Quotient.sameClinicalFact
  (Quotient.externallyRepresentedSubject , Quotient.retainedOrReintroducedHistory) =
  Quotient.stateLegalState
reopenClinicalRelative Quotient.sameClinicalFact
  (Quotient.externallyRepresentedSubject , Quotient.erasedHistory) =
  Quotient.biomedicalState
reopenClinicalRelative Quotient.sameClinicalFact
  (Quotient.livedOriginatingSubject , Quotient.retainedOrReintroducedHistory) =
  Quotient.livedSubjectState
reopenClinicalRelative Quotient.sameClinicalFact
  (Quotient.livedOriginatingSubject , Quotient.erasedHistory) =
  Quotient.livedSubjectState

clinicalRelativeGeometry :
  CoarseFine.CoarseFineReopening Quotient.TranslationState
clinicalRelativeGeometry =
  CoarseFine.coarseFineReopening
    Quotient.ClinicalObservation
    RelativeSemantic
    Quotient.clinicalObserver
    relativeSemantic
    reopenClinicalRelative
    (λ
      { Quotient.stateLegalState → refl
      ; Quotient.biomedicalState → refl
      ; Quotient.livedSubjectState → refl
      })

clinicalPlusRelativeReconstructsState :
  (state : Quotient.TranslationState) →
  CoarseFine.reopen clinicalRelativeGeometry
    (CoarseFine.coarse clinicalRelativeGeometry state)
    (CoarseFine.relativeFine clinicalRelativeGeometry state)
  ≡ state
clinicalPlusRelativeReconstructsState =
  CoarseFine.reopenExact clinicalRelativeGeometry

clinicalRelativeObserverSeparating :
  (left right : Quotient.TranslationState) →
  CoarseFine.coarseFineObserver clinicalRelativeGeometry left
  ≡ CoarseFine.coarseFineObserver clinicalRelativeGeometry right →
  left ≡ right
clinicalRelativeObserverSeparating =
  CoarseFine.coarseFineObserverSeparating clinicalRelativeGeometry

------------------------------------------------------------------------
-- The relative-fine coordinate must change inside a nontrivial clinical fibre.
------------------------------------------------------------------------

stateAndBiomedicalSameClinical :
  CoarseFine.coarse clinicalRelativeGeometry Quotient.stateLegalState
  ≡ CoarseFine.coarse clinicalRelativeGeometry Quotient.biomedicalState
stateAndBiomedicalSameClinical = refl

stateAndBiomedicalDifferent :
  Quotient.stateLegalState ≡ Quotient.biomedicalState → ⊥
stateAndBiomedicalDifferent ()

stateBiomedicalRelativeMustDiffer :
  CoarseFine.relativeFine clinicalRelativeGeometry Quotient.stateLegalState
  ≡ CoarseFine.relativeFine clinicalRelativeGeometry Quotient.biomedicalState → ⊥
stateBiomedicalRelativeMustDiffer =
  CoarseFine.relativeFineMustChangeInsideNontrivialCoarseFibre
    clinicalRelativeGeometry
    stateAndBiomedicalSameClinical
    stateAndBiomedicalDifferent

stateAndLivedSameClinical :
  CoarseFine.coarse clinicalRelativeGeometry Quotient.stateLegalState
  ≡ CoarseFine.coarse clinicalRelativeGeometry Quotient.livedSubjectState
stateAndLivedSameClinical = refl

stateAndLivedDifferent :
  Quotient.stateLegalState ≡ Quotient.livedSubjectState → ⊥
stateAndLivedDifferent ()

stateLivedRelativeMustDiffer :
  CoarseFine.relativeFine clinicalRelativeGeometry Quotient.stateLegalState
  ≡ CoarseFine.relativeFine clinicalRelativeGeometry Quotient.livedSubjectState → ⊥
stateLivedRelativeMustDiffer =
  CoarseFine.relativeFineMustChangeInsideNontrivialCoarseFibre
    clinicalRelativeGeometry
    stateAndLivedSameClinical
    stateAndLivedDifferent

------------------------------------------------------------------------
-- A coarse clinical quotient can therefore be exact for a clinical consumer
-- while remaining insufficient for fine-sensitive subject/history consumers.
------------------------------------------------------------------------

record DrugCategoryClinicalQuotientRelativeFibreBoundary : Set where
  constructor drugCategoryClinicalQuotientRelativeFibreBoundary
  field
    clinicalObservationIsCoarseQuotient : Bool
    clinicalObservationIsCoarseQuotientIsTrue :
      clinicalObservationIsCoarseQuotient ≡ true
    subjectHistoryRemainRelativeFineResidual : Bool
    subjectHistoryRemainRelativeFineResidualIsTrue :
      subjectHistoryRemainRelativeFineResidual ≡ true
    coarsePlusRelativeFineReconstructsStateExactly : Bool
    coarsePlusRelativeFineReconstructsStateExactlyIsTrue :
      coarsePlusRelativeFineReconstructsStateExactly ≡ true
    sameClinicalObservationDeterminesWholeSemanticState : Bool
    sameClinicalObservationDeterminesWholeSemanticStateIsFalse :
      sameClinicalObservationDeterminesWholeSemanticState ≡ false
    retainingRelativeFineResidualIsRequiredToUseClinicalQuotient : Bool
    retainingRelativeFineResidualIsRequiredToUseClinicalQuotientIsFalse :
      retainingRelativeFineResidualIsRequiredToUseClinicalQuotient ≡ false

canonicalDrugCategoryClinicalQuotientRelativeFibreBoundary :
  DrugCategoryClinicalQuotientRelativeFibreBoundary
canonicalDrugCategoryClinicalQuotientRelativeFibreBoundary =
  drugCategoryClinicalQuotientRelativeFibreBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
