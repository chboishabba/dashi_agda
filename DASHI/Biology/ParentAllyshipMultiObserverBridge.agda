module DASHI.Biology.ParentAllyshipMultiObserverBridge where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.EducationCorpusSourceRegistry as Sources

------------------------------------------------------------------------
-- Parent allyship / multi-observer bridge.
--
-- Three dyslexia papers are retained as distinct source surfaces: a
-- conceptual lens, an empirical advocacy/allyship distinction, and a study of
-- parent-perceived barriers to meaningful parent-school partnership.

data ObserverFibre : Set where
  studentObserver : ObserverFibre
  parentAllyObserver : ObserverFibre
  teacherObserver : ObserverFibre
  researcherObserver : ObserverFibre
  institutionObserver : ObserverFibre
  modelObserver : ObserverFibre

canonicalObserverFibres : List ObserverFibre
canonicalObserverFibres =
  studentObserver
  ∷ parentAllyObserver
  ∷ teacherObserver
  ∷ researcherObserver
  ∷ institutionObserver
  ∷ modelObserver
  ∷ []

data ExperienceProximity : Set where
  primaryExperience : ExperienceProximity
  vicariousExperience : ExperienceProximity
  primaryAdjacentExperience : ExperienceProximity

canonicalExperienceProximities : List ExperienceProximity
canonicalExperienceProximities =
  primaryExperience ∷ vicariousExperience ∷ primaryAdjacentExperience ∷ []

record ObserverProjection : Set where
  constructor mkObserverProjection
  field
    observer : ObserverFibre
    projectionLabel : String
    projectionIsSituated : Bool
    projectionIsSituatedIsTrue : projectionIsSituated ≡ true
    projectionNotWholeSystem : Bool
    projectionNotWholeSystemIsTrue : projectionNotWholeSystem ≡ true
    projectionCannotEraseOtherObservers : Bool
    projectionCannotEraseOtherObserversIsTrue :
      projectionCannotEraseOtherObservers ≡ true

open ObserverProjection public

canonicalStudentProjection : ObserverProjection
canonicalStudentProjection =
  mkObserverProjection studentObserver "student lived and epistemic surface"
    true refl true refl true refl

canonicalParentProjection : ObserverProjection
canonicalParentProjection =
  mkObserverProjection parentAllyObserver
    "parent ally primary-adjacent and vicarious experience surface"
    true refl true refl true refl

canonicalTeacherProjection : ObserverProjection
canonicalTeacherProjection =
  mkObserverProjection teacherObserver "teacher practice and institutional interface surface"
    true refl true refl true refl

canonicalResearcherProjection : ObserverProjection
canonicalResearcherProjection =
  mkObserverProjection researcherObserver "researcher interpretation surface"
    true refl true refl true refl

canonicalInstitutionProjection : ObserverProjection
canonicalInstitutionProjection =
  mkObserverProjection institutionObserver "policy and administrative record surface"
    true refl true refl true refl

canonicalModelProjection : ObserverProjection
canonicalModelProjection =
  mkObserverProjection modelObserver "machine-classification proxy surface"
    true refl true refl true refl

canonicalObserverProjections : List ObserverProjection
canonicalObserverProjections =
  canonicalStudentProjection
  ∷ canonicalParentProjection
  ∷ canonicalTeacherProjection
  ∷ canonicalResearcherProjection
  ∷ canonicalInstitutionProjection
  ∷ canonicalModelProjection
  ∷ []

record ParentAllyshipMultiObserverBridge : Set where
  constructor mkParentAllyshipMultiObserverBridge
  field
    conceptualLensPaper : Sources.PaperReference
    conceptualLensPaperIsCanonical :
      conceptualLensPaper ≡ Sources.parentalAllyshipLensPaper
    advocacyAllyshipPaper : Sources.PaperReference
    advocacyAllyshipPaperIsCanonical :
      advocacyAllyshipPaper ≡ Sources.advocacyAllyshipPaper
    partnershipBarriersPaper : Sources.PaperReference
    partnershipBarriersPaperIsCanonical :
      partnershipBarriersPaper ≡ Sources.partnershipBarriersPaper
    observerFibres : List ObserverFibre
    observerFibresAreCanonical : observerFibres ≡ canonicalObserverFibres
    experienceProximities : List ExperienceProximity
    experienceProximitiesAreCanonical :
      experienceProximities ≡ canonicalExperienceProximities
    projections : List ObserverProjection
    projectionsAreCanonical : projections ≡ canonicalObserverProjections
    parentExpertiseMayBeEvidence : Bool
    parentExpertiseMayBeEvidenceIsTrue : parentExpertiseMayBeEvidence ≡ true
    childVoiceRemainsDistinct : Bool
    childVoiceRemainsDistinctIsTrue : childVoiceRemainsDistinct ≡ true
    policyNotEnactment : Bool
    policyNotEnactmentIsTrue : policyNotEnactment ≡ true
    parentPerceptionNotInstitutionalIntentProof : Bool
    parentPerceptionNotInstitutionalIntentProofIsTrue :
      parentPerceptionNotInstitutionalIntentProof ≡ true
    noObserverProjectionEqualsWhole : Bool
    noObserverProjectionEqualsWholeIsTrue :
      noObserverProjectionEqualsWhole ≡ true
    reading : String

open ParentAllyshipMultiObserverBridge public

canonicalParentAllyshipMultiObserverBridge :
  ParentAllyshipMultiObserverBridge
canonicalParentAllyshipMultiObserverBridge =
  mkParentAllyshipMultiObserverBridge
    Sources.parentalAllyshipLensPaper refl
    Sources.advocacyAllyshipPaper refl
    Sources.partnershipBarriersPaper refl
    canonicalObserverFibres refl
    canonicalExperienceProximities refl
    canonicalObserverProjections refl
    true refl
    true refl
    true refl
    true refl
    true refl
    "Parent allyship is retained as a situated observer fibre carrying primary-adjacent and vicarious disability experience and potentially important expertise. It does not replace the child's primary experience or voice. Parent, student, teacher, researcher, institution and model projections remain plural local sections rather than a single complete system view."
