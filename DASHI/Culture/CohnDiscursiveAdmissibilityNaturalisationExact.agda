module DASHI.Culture.CohnDiscursiveAdmissibilityNaturalisationExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Culture.CohnTechnostrategicDiscourseExact as Cohn
import DASHI.Culture.CohnTechnostrategicSourceAtlasExact as Sources
import DASHI.Education.CapabilityRecognitionExact as Recognition

------------------------------------------------------------------------
-- COHN / DISCURSIVE ADMISSIBILITY / NATURALISATION
--
-- The reusable DASHI separation is:
--
--   materially/situationally real
--        != expressible in the expert vocabulary
--        != admissible inside the expert discourse
--        != institutionally normalised
--        != adequate for every consumer query.
--
-- Cohn's work supplies a bounded discourse-analysis fixture.  The finite
-- carriers and non-factorability proofs below are DASHI constructions.
------------------------------------------------------------------------

data DiscursiveState : Set where
  outsideVocabularyConsequential : DiscursiveState
  outsideVocabularyIrrelevant : DiscursiveState
  expressibleRejected : DiscursiveState
  expressibleAdmitted : DiscursiveState

expressionProjection : DiscursiveState → Bool
expressionProjection outsideVocabularyConsequential = false
expressionProjection outsideVocabularyIrrelevant = false
expressionProjection expressibleRejected = true
expressionProjection expressibleAdmitted = true

admissibilityProjection : DiscursiveState → Bool
admissibilityProjection outsideVocabularyConsequential = false
admissibilityProjection outsideVocabularyIrrelevant = false
admissibilityProjection expressibleRejected = false
admissibilityProjection expressibleAdmitted = true

materialRelevanceProjection : DiscursiveState → Bool
materialRelevanceProjection outsideVocabularyConsequential = true
materialRelevanceProjection outsideVocabularyIrrelevant = false
materialRelevanceProjection expressibleRejected = true
materialRelevanceProjection expressibleAdmitted = true

------------------------------------------------------------------------
-- Expression does not determine admissibility.
------------------------------------------------------------------------

sameExpressionDifferentAdmissibility :
  expressionProjection expressibleRejected
  ≡ expressionProjection expressibleAdmitted
sameExpressionDifferentAdmissibility = refl

admissibilityDiffersAtSameExpression :
  admissibilityProjection expressibleRejected
  ≡ admissibilityProjection expressibleAdmitted → ⊥
admissibilityDiffersAtSameExpression ()

expressionAdmissibilityCollision :
  NonFactor.NonFactorabilityWitness
    expressionProjection admissibilityProjection
expressionAdmissibilityCollision =
  NonFactor.nonFactorabilityWitness
    expressibleRejected expressibleAdmitted
    sameExpressionDifferentAdmissibility
    admissibilityDiffersAtSameExpression

expressionSurfaceCannotDetermineAdmissibility :
  NonFactor.FactorsThrough expressionProjection admissibilityProjection → ⊥
expressionSurfaceCannotDetermineAdmissibility =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    expressionAdmissibilityCollision

------------------------------------------------------------------------
-- Inadmissibility does not determine material irrelevance.
--
-- Two states can both lie outside the discourse's admissible surface while
-- differing on the external material/situational consumer query.
------------------------------------------------------------------------

sameInadmissibilityDifferentMaterialRelevance :
  admissibilityProjection outsideVocabularyConsequential
  ≡ admissibilityProjection outsideVocabularyIrrelevant
sameInadmissibilityDifferentMaterialRelevance = refl

materialRelevanceDiffersAtSameInadmissibility :
  materialRelevanceProjection outsideVocabularyConsequential
  ≡ materialRelevanceProjection outsideVocabularyIrrelevant → ⊥
materialRelevanceDiffersAtSameInadmissibility ()

inadmissibilityMaterialCollision :
  NonFactor.NonFactorabilityWitness
    admissibilityProjection materialRelevanceProjection
inadmissibilityMaterialCollision =
  NonFactor.nonFactorabilityWitness
    outsideVocabularyConsequential outsideVocabularyIrrelevant
    sameInadmissibilityDifferentMaterialRelevance
    materialRelevanceDiffersAtSameInadmissibility

admissibilityCannotDetermineMaterialRelevance :
  NonFactor.FactorsThrough
    admissibilityProjection materialRelevanceProjection → ⊥
admissibilityCannotDetermineMaterialRelevance =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    inadmissibilityMaterialCollision

------------------------------------------------------------------------
-- Explicit existence-before-legibility reuse.
--
-- CapabilityRecognitionExact already proves that capability can be present
-- before it is reachable, socially legible, or institutionally recognised.
-- We import that exact boundary rather than manufacturing a discourse-specific
-- duplicate theorem.
------------------------------------------------------------------------

recognitionLegibilityBoundary : Recognition.CapabilityRecognitionBoundary
recognitionLegibilityBoundary = Recognition.canonicalCapabilityRecognitionBoundary

latentCapabilityRemainsPresentBeforeLegibility :
  Recognition.capabilityPresent Recognition.latentUnrecognised ≡ true ×
  Recognition.contributionLegible Recognition.latentUnrecognised ≡ false ×
  Recognition.contributionRecognised Recognition.latentUnrecognised ≡ false
latentCapabilityRemainsPresentBeforeLegibility = refl , (refl , refl)

------------------------------------------------------------------------
-- Naturalisation / normalisation is not consumer adequacy.
--
-- Institutional routine can stabilise both an adequate and an inadequate
-- practice.  Therefore the fact that a discourse/practice is normalised cannot
-- by itself determine whether it preserves the consumer-relevant coordinate.
------------------------------------------------------------------------

data PracticeState : Set where
  normalisedAdequate : PracticeState
  normalisedInadequate : PracticeState

normalisationProjection : PracticeState → Bool
normalisationProjection normalisedAdequate = true
normalisationProjection normalisedInadequate = true

adequacyProjection : PracticeState → Bool
adequacyProjection normalisedAdequate = true
adequacyProjection normalisedInadequate = false

sameNormalisationDifferentAdequacy :
  normalisationProjection normalisedAdequate
  ≡ normalisationProjection normalisedInadequate
sameNormalisationDifferentAdequacy = refl

adequacyDiffersAtSameNormalisation :
  adequacyProjection normalisedAdequate
  ≡ adequacyProjection normalisedInadequate → ⊥
adequacyDiffersAtSameNormalisation ()

normalisationAdequacyCollision :
  NonFactor.NonFactorabilityWitness
    normalisationProjection adequacyProjection
normalisationAdequacyCollision =
  NonFactor.nonFactorabilityWitness
    normalisedAdequate normalisedInadequate
    sameNormalisationDifferentAdequacy
    adequacyDiffersAtSameNormalisation

normalisedPracticeCannotDetermineAdequacy :
  NonFactor.FactorsThrough normalisationProjection adequacyProjection → ⊥
normalisedPracticeCannotDetermineAdequacy =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    normalisationAdequacyCollision

------------------------------------------------------------------------
-- Cross-pollination retains parent ownership.
------------------------------------------------------------------------

cohnConsumerAdequacyBoundary : Cohn.CohnTechnostrategicBoundary
cohnConsumerAdequacyBoundary = Cohn.canonicalCohnTechnostrategicBoundary

cohnSourceBoundary : Sources.CohnSourceBoundary
cohnSourceBoundary = Sources.canonicalCohnSourceBoundary

------------------------------------------------------------------------
-- WrongType / no-promotion boundary.
------------------------------------------------------------------------

record DiscursiveAdmissibilityBoundary : Set where
  constructor discursiveAdmissibilityBoundary
  field
    unexpressibleImpliesUnreal : Bool
    unexpressibleImpliesUnrealIsFalse : unexpressibleImpliesUnreal ≡ false
    inadmissibleImpliesMateriallyIrrelevant : Bool
    inadmissibleImpliesMateriallyIrrelevantIsFalse :
      inadmissibleImpliesMateriallyIrrelevant ≡ false
    discursivelyAdmittedImpliesTrue : Bool
    discursivelyAdmittedImpliesTrueIsFalse :
      discursivelyAdmittedImpliesTrue ≡ false
    institutionallyNormalisedImpliesAdequate : Bool
    institutionallyNormalisedImpliesAdequateIsFalse :
      institutionallyNormalisedImpliesAdequate ≡ false
    expertRecognitionCreatesReality : Bool
    expertRecognitionCreatesRealityIsFalse :
      expertRecognitionCreatesReality ≡ false
    expandedVocabularyCreatesAuthority : Bool
    expandedVocabularyCreatesAuthorityIsFalse :
      expandedVocabularyCreatesAuthority ≡ false
    externalMaterialCoordinateMayRequireObserverRefinement : Bool
    externalMaterialCoordinateMayRequireObserverRefinementIsTrue :
      externalMaterialCoordinateMayRequireObserverRefinement ≡ true

open DiscursiveAdmissibilityBoundary public

canonicalDiscursiveAdmissibilityBoundary : DiscursiveAdmissibilityBoundary
canonicalDiscursiveAdmissibilityBoundary =
  discursiveAdmissibilityBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
