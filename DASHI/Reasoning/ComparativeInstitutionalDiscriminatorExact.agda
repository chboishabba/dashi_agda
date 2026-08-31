module DASHI.Reasoning.ComparativeInstitutionalDiscriminatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Reasoning.ComparativeInstitutionalMeaningExact as Comparative

------------------------------------------------------------------------
-- COMPARATIVE INSTITUTIONAL CONTRAST -> DISCRIMINATOR SYNTHESIS
--
-- A structural interpretation becomes experimentally useful when we can name
-- a prospective observation that separates institutional worlds which are
-- currently collapsed by the existing observer. This does not itself prove the
-- structural interpretation; it identifies a measurement/design capable of
-- reducing that ambiguity.
------------------------------------------------------------------------

record InstitutionalComparisonProblem : Set₁ where
  constructor institutionalComparisonProblem
  field
    World : Set
    ExistingObservation : Set
    existingObserve : World → ExistingObservation
    actual alternative : World
    currentlyCollapsed :
      existingObserve actual ≡ existingObserve alternative
    structuralReference : String
    matchingReference : String

open InstitutionalComparisonProblem public

comparisonCollision :
  (problem : InstitutionalComparisonProblem) →
  Discriminator.CurrentObserverCollision (existingObserve problem)
comparisonCollision problem =
  Discriminator.currentObserverCollision
    (actual problem)
    (alternative problem)
    (currentlyCollapsed problem)

record InstitutionalDiscriminator
    (problem : InstitutionalComparisonProblem) : Set₁ where
  constructor institutionalDiscriminator
  field
    bundle : Discriminator.ExperimentBundle (World problem)
    separatesWorlds :
      Discriminator.BundleSeparates bundle
        (actual problem)
        (alternative problem)
    designReference : String
    calibrationReference : String
    nuisanceAuditReference : String
    institutionalInterpretationReference : String

open InstitutionalDiscriminator public

asLanguageExtension :
  ∀ {problem} →
  InstitutionalDiscriminator problem →
  Discriminator.DiscriminatingLanguageExtension
    (existingObserve problem)
asLanguageExtension {problem} discriminator =
  Discriminator.discriminatingLanguageExtension
    (comparisonCollision problem)
    (bundle discriminator)
    (separatesWorlds discriminator)

------------------------------------------------------------------------
-- Candidate study kinds remain design classes, not evidence by themselves.
------------------------------------------------------------------------

data InstitutionalStudyKind : Set where
  matchedJurisdictionStudy
  regulatoryDiscontinuityStudy
  longitudinalEnforcementChangeStudy
  ownershipProvisioningContrastStudy
  naturalExperimentStudy
  policyTransitionStudy
  : InstitutionalStudyKind

record CandidateInstitutionalStudy
    (problem : InstitutionalComparisonProblem) : Set₁ where
  constructor candidateInstitutionalStudy
  field
    kind : InstitutionalStudyKind
    proposedBundle : Discriminator.ExperimentBundle (World problem)
    comparisonCoordinateReference : String
    matchingPlanReference : String
    nuisancePlanReference : String
    calibrationStillRequiredReference : String

open CandidateInstitutionalStudy public

record AdmittedInstitutionalStudy
    {problem : InstitutionalComparisonProblem}
    (candidate : CandidateInstitutionalStudy problem) : Set₁ where
  constructor admittedInstitutionalStudy
  field
    separates :
      Discriminator.BundleSeparates
        (proposedBundle candidate)
        (actual problem)
        (alternative problem)
    admissionReference : String
    empiricalRealizationReference : String

open AdmittedInstitutionalStudy public

admittedStudyAsDiscriminator :
  ∀ {problem candidate} →
  AdmittedInstitutionalStudy {problem} candidate →
  InstitutionalDiscriminator problem
admittedStudyAsDiscriminator {candidate = candidate} admitted =
  institutionalDiscriminator
    (proposedBundle candidate)
    (separates admitted)
    (comparisonCoordinateReference candidate)
    (calibrationStillRequiredReference candidate)
    (nuisancePlanReference candidate)
    (admissionReference admitted)

record ComparativeInstitutionalDiscriminatorBoundary : Set where
  constructor comparativeInstitutionalDiscriminatorBoundary
  field
    namingStudyDesignProvesStructuralInterpretation : Bool
    namingStudyDesignProvesStructuralInterpretationIsFalse :
      namingStudyDesignProvesStructuralInterpretation ≡ false
    admittedStudyMustSeparateDeclaredWorlds : Bool
    admittedStudyMustSeparateDeclaredWorldsIsTrue :
      admittedStudyMustSeparateDeclaredWorlds ≡ true
    discriminatorExtendsObservationLanguage : Bool
    discriminatorExtendsObservationLanguageIsTrue :
      discriminatorExtendsObservationLanguage ≡ true
    pairwiseWorldSeparationProvesCompletePoliticalEconomyTheory : Bool
    pairwiseWorldSeparationProvesCompletePoliticalEconomyTheoryIsFalse :
      pairwiseWorldSeparationProvesCompletePoliticalEconomyTheory ≡ false

canonicalComparativeInstitutionalDiscriminatorBoundary :
  ComparativeInstitutionalDiscriminatorBoundary
canonicalComparativeInstitutionalDiscriminatorBoundary =
  comparativeInstitutionalDiscriminatorBoundary
    false refl
    true refl
    true refl
    false refl
