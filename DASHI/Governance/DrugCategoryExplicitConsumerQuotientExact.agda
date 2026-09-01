module DASHI.Governance.DrugCategoryExplicitConsumerQuotientExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.DrugCategoryMultiChartTranslationGeometryExact as Translation
import DASHI.Governance.DrugCategoryPartialTranslationPathCategoryExact as Path
import DASHI.Governance.DrugCategoryConsumerIndexedTranslationAdmissionExact as Admission
import DASHI.Governance.DrugCategoryConsumerRelativeQuotientInverseExact as Inverse

------------------------------------------------------------------------
-- EXPLICIT CONSUMER QUOTIENT
--
-- A consumer quotient is represented by the observer-induced equivalence
--
--     x ~Q y  iff  Q x = Q y.
--
-- We do not identify this observational quotient with a quotient type carrying
-- every semantic/history/authority coordinate.  A chart translation descends
-- exactly when it preserves the declared observer.
------------------------------------------------------------------------

data TranslationState : Set where
  stateLegalState
  biomedicalState
  livedSubjectState
  : TranslationState

data ClinicalObservation : Set where
  sameClinicalFact : ClinicalObservation

data SubjectObservation : Set where
  externallyRepresentedSubject
  livedOriginatingSubject
  : SubjectObservation

data HistoryObservation : Set where
  erasedHistory
  retainedOrReintroducedHistory
  : HistoryObservation

clinicalObserver : TranslationState → ClinicalObservation
clinicalObserver stateLegalState = sameClinicalFact
clinicalObserver biomedicalState = sameClinicalFact
clinicalObserver livedSubjectState = sameClinicalFact

subjectObserver : TranslationState → SubjectObservation
subjectObserver stateLegalState = externallyRepresentedSubject
subjectObserver biomedicalState = externallyRepresentedSubject
subjectObserver livedSubjectState = livedOriginatingSubject

historyObserver : TranslationState → HistoryObservation
historyObserver stateLegalState = retainedOrReintroducedHistory
historyObserver biomedicalState = erasedHistory
historyObserver livedSubjectState = retainedOrReintroducedHistory

ObserverEquivalent :
  ∀ {Observation : Set} →
  (TranslationState → Observation) →
  TranslationState → TranslationState → Set
ObserverEquivalent observer left right = observer left ≡ observer right

clinicalStateEquivalent :
  ObserverEquivalent clinicalObserver stateLegalState biomedicalState
clinicalStateEquivalent = refl

clinicalBiomedicalLivedEquivalent :
  ObserverEquivalent clinicalObserver biomedicalState livedSubjectState
clinicalBiomedicalLivedEquivalent = refl

clinicalStateLivedEquivalent :
  ObserverEquivalent clinicalObserver stateLegalState livedSubjectState
clinicalStateLivedEquivalent =
  trans clinicalStateEquivalent clinicalBiomedicalLivedEquivalent

subjectStateLivedNotEquivalent :
  ObserverEquivalent subjectObserver stateLegalState livedSubjectState → ⊥
subjectStateLivedNotEquivalent ()

historyStateBiomedicalNotEquivalent :
  ObserverEquivalent historyObserver stateLegalState biomedicalState → ⊥
historyStateBiomedicalNotEquivalent ()

------------------------------------------------------------------------
-- Descent through a coarse observer.
------------------------------------------------------------------------

record DescendsThrough
    {Observation QuotientObservation : Set}
    (fineObserver : TranslationState → Observation)
    (quotientObserver : TranslationState → QuotientObservation) : Set where
  constructor descendsThrough
  field
    readOnQuotient : QuotientObservation → Observation
    commutes :
      (state : TranslationState) →
      fineObserver state ≡ readOnQuotient (quotientObserver state)

open DescendsThrough public

clinicalDescendsThroughClinical :
  DescendsThrough clinicalObserver clinicalObserver
clinicalDescendsThroughClinical =
  descendsThrough (λ observation → observation) (λ state → refl)

------------------------------------------------------------------------
-- A subject-sensitive observer cannot descend through the clinical quotient:
-- state/legal and lived states collide clinically but subject-observer differs.
------------------------------------------------------------------------

subjectCannotDescendThroughClinical :
  DescendsThrough subjectObserver clinicalObserver → ⊥
subjectCannotDescendThroughClinical descent =
  subjectStateLivedNotEquivalent
    (trans
      (commutes descent stateLegalState)
      (trans
        (cong (readOnQuotient descent) clinicalStateLivedEquivalent)
        (sym (commutes descent livedSubjectState))))

historyCannotDescendThroughClinical :
  DescendsThrough historyObserver clinicalObserver → ⊥
historyCannotDescendThroughClinical descent =
  historyStateBiomedicalNotEquivalent
    (trans
      (commutes descent stateLegalState)
      (trans
        (cong (readOnQuotient descent) clinicalStateEquivalent)
        (sym (commutes descent biomedicalState))))

------------------------------------------------------------------------
-- Consumer-relative inverse weld.
------------------------------------------------------------------------

clinicalQuotientInverse :
  Inverse.ConsumerRelativeQuotientInverse
    Admission.clinicalSafetyConsumer
    Path.stateClinicalLivedPath
clinicalQuotientInverse =
  Inverse.clinicalQuotientInverseOnStateClinicalLived

subjectQuotientInverseImpossible :
  Inverse.ConsumerRelativeQuotientInverse
    Admission.livedSubjectAuthorityConsumer
    Path.stateClinicalLivedPath → ⊥
subjectQuotientInverseImpossible =
  Inverse.livedSubjectQuotientNotInvertibleOnStateClinicalLived

historyQuotientInverseImpossible :
  Inverse.ConsumerRelativeQuotientInverse
    Admission.historicalContinuityConsumer
    Path.stateClinicalLivedPath → ⊥
historyQuotientInverseImpossible =
  Inverse.historicalQuotientNotInvertibleOnStateClinicalLived

------------------------------------------------------------------------
-- Nonfactorability witness: clinical observation cannot recover subject state.
------------------------------------------------------------------------

clinicalCannotRecoverSubjectObservation :
  INF.FactorsThrough clinicalObserver subjectObserver → ⊥
clinicalCannotRecoverSubjectObservation =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      stateLegalState
      livedSubjectState
      refl
      subjectStateLivedNotEquivalent)

------------------------------------------------------------------------
-- Hard boundaries.
------------------------------------------------------------------------

data ClinicalQuotientPromotesWholeSemanticQuotient : Set where

data ObserverEquivalencePromotesStateIdentity : Set where

data QuotientDescentPromotesHistoricalRecovery : Set where

clinicalQuotientDoesNotPromoteWholeSemanticQuotient :
  ClinicalQuotientPromotesWholeSemanticQuotient → ⊥
clinicalQuotientDoesNotPromoteWholeSemanticQuotient ()

observerEquivalenceDoesNotPromoteStateIdentity :
  ObserverEquivalencePromotesStateIdentity → ⊥
observerEquivalenceDoesNotPromoteStateIdentity ()

quotientDescentDoesNotPromoteHistoricalRecovery :
  QuotientDescentPromotesHistoricalRecovery → ⊥
quotientDescentDoesNotPromoteHistoricalRecovery ()

record DrugCategoryExplicitConsumerQuotientBoundary : Set where
  constructor drugCategoryExplicitConsumerQuotientBoundary
  field
    consumerEquivalenceIsObserverEquality : Bool
    consumerEquivalenceIsObserverEqualityIsTrue :
      consumerEquivalenceIsObserverEquality ≡ true
    clinicalObserverDescendsThroughClinicalQuotient : Bool
    clinicalObserverDescendsThroughClinicalQuotientIsTrue :
      clinicalObserverDescendsThroughClinicalQuotient ≡ true
    subjectObserverDescendsThroughClinicalQuotient : Bool
    subjectObserverDescendsThroughClinicalQuotientIsFalse :
      subjectObserverDescendsThroughClinicalQuotient ≡ false
    historyObserverDescendsThroughClinicalQuotient : Bool
    historyObserverDescendsThroughClinicalQuotientIsFalse :
      historyObserverDescendsThroughClinicalQuotient ≡ false
    clinicalQuotientInverseMeansWholeChartInverse : Bool
    clinicalQuotientInverseMeansWholeChartInverseIsFalse :
      clinicalQuotientInverseMeansWholeChartInverse ≡ false

canonicalDrugCategoryExplicitConsumerQuotientBoundary :
  DrugCategoryExplicitConsumerQuotientBoundary
canonicalDrugCategoryExplicitConsumerQuotientBoundary =
  drugCategoryExplicitConsumerQuotientBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
