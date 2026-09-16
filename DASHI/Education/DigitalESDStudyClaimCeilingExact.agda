module DASHI.Education.DigitalESDStudyClaimCeilingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Design
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone
import DASHI.Biology.CausalEstimandStatisticalRealisationExact as Statistical
import DASHI.Biology.CausalEstimatorGuaranteesExact as Guarantees

------------------------------------------------------------------------
-- DIGITAL-ESD STUDY CLAIM CEILING
--
-- Thin application adapter over existing design, implication-cone and
-- statistical-estimation machinery. Every included paper may contribute only
-- claims supported by its own design, population, realised sample, measurement,
-- uncertainty and transport receipts. Missing numerical/statistical material
-- is retained as missing rather than reconstructed from narrative confidence.
------------------------------------------------------------------------

data ReportingState : Set where
  explicitlyReported : ReportingState
  derivableWithSameObjectReceipt : ReportingState
  notReported : ReportingState

data ReportedNat : Set where
  explicitlyReportedNat : Nat → String → ReportedNat
  derivedNatWithSameObjectReceipt : Nat → String → String → ReportedNat
  natNotReported : String → ReportedNat

record ReportedSurface : Set where
  constructor reported-surface
  field
    reportingState : ReportingState
    surfaceReference : String
    locatorReference : String
    interpretationReference : String

open ReportedSurface public

------------------------------------------------------------------------
-- Source-reported study design remains primary.
--
-- The generic EvidenceDesignAdmissibility ontology is deliberately finite and
-- does not contain every design label used in the literature. A source may
-- therefore remain unmapped rather than being forced into the nearest existing
-- constructor. Mapping is a separate, explicit receipt.
------------------------------------------------------------------------

data DesignReceiptStatus : Set where
  canonicalDesignReceipt : Design.StudyDesignReceipt → DesignReceiptStatus
  sourceReportedDesignUnmapped : String → String → DesignReceiptStatus

data StudyClaimCoordinate : Set where
  sourcePopulationCoordinate : StudyClaimCoordinate
  enrolledOrReportedNCoordinate : StudyClaimCoordinate
  analysisNCoordinate : StudyClaimCoordinate
  allocationCoordinate : StudyClaimCoordinate
  comparatorCoordinate : StudyClaimCoordinate
  measurementValidityCoordinate : StudyClaimCoordinate
  attritionMissingnessCoordinate : StudyClaimCoordinate
  confoundingControlCoordinate : StudyClaimCoordinate
  implementationFidelityCoordinate : StudyClaimCoordinate
  multiplicityCoordinate : StudyClaimCoordinate
  effectSizeCoordinate : StudyClaimCoordinate
  uncertaintyIntervalCoordinate : StudyClaimCoordinate
  timeHorizonCoordinate : StudyClaimCoordinate
  externalValidityCoordinate : StudyClaimCoordinate
  participantRoleCoordinate : StudyClaimCoordinate
  implicationCeilingCoordinate : StudyClaimCoordinate

studyClaimCoordinates : List StudyClaimCoordinate
studyClaimCoordinates =
  sourcePopulationCoordinate
  ∷ enrolledOrReportedNCoordinate
  ∷ analysisNCoordinate
  ∷ allocationCoordinate
  ∷ comparatorCoordinate
  ∷ measurementValidityCoordinate
  ∷ attritionMissingnessCoordinate
  ∷ confoundingControlCoordinate
  ∷ implementationFidelityCoordinate
  ∷ multiplicityCoordinate
  ∷ effectSizeCoordinate
  ∷ uncertaintyIntervalCoordinate
  ∷ timeHorizonCoordinate
  ∷ externalValidityCoordinate
  ∷ participantRoleCoordinate
  ∷ implicationCeilingCoordinate
  ∷ []

studyClaimCoordinateCount : Nat
studyClaimCoordinateCount = 16

record StudyClaimProfile : Set where
  constructor study-claim-profile
  field
    studyKey : String
    source : Attr.AttributedSource
    sourceRoleReference : String
    sourceLocatorReference : String
    reportedDesignReference : String
    designReceiptStatus : DesignReceiptStatus
    sourcePopulationReference : String
    enrolledOrReportedN : ReportedNat
    analysisN : ReportedNat
    allocationReference : String
    comparatorReference : String
    measurementValidityReference : String
    attritionMissingnessReference : String
    confoundingControlReference : String
    implementationFidelityReference : String
    multiplicityReference : String
    effectSizeSurface : ReportedSurface
    uncertaintyIntervalSurface : ReportedSurface
    timeHorizonReference : String
    externalValidityReference : String
    participantRole : Design.EpistemicRole
    strongestSupportedImplication : Cone.ImplicationKind
    strongestSupportedImplicationReference : String
    explicitLimitationsReference : String

open StudyClaimProfile public

------------------------------------------------------------------------
-- Canonical owner reuse. These are the theories that give meaning to the
-- design/claim ceiling; this module does not replace them.
------------------------------------------------------------------------

designBoundary : Design.EvidenceDesignBoundary
designBoundary = Design.canonicalEvidenceDesignBoundary

implicationConeBoundary : Cone.ExperimentalAssertionConeBoundary
implicationConeBoundary = Cone.canonicalExperimentalAssertionConeBoundary

statisticalBoundary : Statistical.CausalEstimandStatisticalRealisationBoundary
statisticalBoundary = Statistical.canonicalCausalEstimandStatisticalRealisationBoundary

guaranteeBoundary : Guarantees.CausalEstimatorGuaranteeBoundary
guaranteeBoundary = Guarantees.canonicalCausalEstimatorGuaranteeBoundary

------------------------------------------------------------------------
-- Non-promotion firewalls.
------------------------------------------------------------------------

data ReportedPValueCreatesCausalIdentification : Set where
data LargeSampleCreatesRepresentativePopulation : Set where
data ConfidenceIntervalCreatesPopulationTransport : Set where
data QualitativeFindingCreatesPopulationPrevalence : Set where
data StudyFindingCreatesSystemTransformation : Set where
data MissingUncertaintyMayBeInvented : Set where
data NarrowIntervalCreatesMechanismIdentification : Set where
data StatisticalSignificanceCreatesPracticalSignificance : Set where
data AssociationCreatesPracticeRecommendation : Set where
data UnmappedDesignMayBeForcedIntoNearestCanonicalKind : Set where

reportedPValueDoesNotCreateCausalIdentification :
  ReportedPValueCreatesCausalIdentification → ⊥
reportedPValueDoesNotCreateCausalIdentification ()

largeSampleDoesNotCreateRepresentativePopulation :
  LargeSampleCreatesRepresentativePopulation → ⊥
largeSampleDoesNotCreateRepresentativePopulation ()

confidenceIntervalDoesNotCreatePopulationTransport :
  ConfidenceIntervalCreatesPopulationTransport → ⊥
confidenceIntervalDoesNotCreatePopulationTransport ()

qualitativeFindingDoesNotCreatePopulationPrevalence :
  QualitativeFindingCreatesPopulationPrevalence → ⊥
qualitativeFindingDoesNotCreatePopulationPrevalence ()

studyFindingDoesNotCreateSystemTransformation :
  StudyFindingCreatesSystemTransformation → ⊥
studyFindingDoesNotCreateSystemTransformation ()

missingUncertaintyMayNotBeInvented : MissingUncertaintyMayBeInvented → ⊥
missingUncertaintyMayNotBeInvented ()

narrowIntervalDoesNotCreateMechanismIdentification :
  NarrowIntervalCreatesMechanismIdentification → ⊥
narrowIntervalDoesNotCreateMechanismIdentification ()

statisticalSignificanceDoesNotCreatePracticalSignificance :
  StatisticalSignificanceCreatesPracticalSignificance → ⊥
statisticalSignificanceDoesNotCreatePracticalSignificance ()

associationDoesNotCreatePracticeRecommendation :
  AssociationCreatesPracticeRecommendation → ⊥
associationDoesNotCreatePracticeRecommendation ()

unmappedDesignMayNotBeForcedIntoNearestCanonicalKind :
  UnmappedDesignMayBeForcedIntoNearestCanonicalKind → ⊥
unmappedDesignMayNotBeForcedIntoNearestCanonicalKind ()

------------------------------------------------------------------------
-- Review-level boundary.
------------------------------------------------------------------------

record StudyClaimCeilingBoundary : Set where
  constructor study-claim-ceiling-boundary
  field
    attributedSourceObjectRetained : Bool
    attributedSourceObjectRetainedIsTrue : attributedSourceObjectRetained ≡ true
    sourceReportedDesignRetained : Bool
    sourceReportedDesignRetainedIsTrue : sourceReportedDesignRetained ≡ true
    unresolvedDesignMappingPermitted : Bool
    unresolvedDesignMappingPermittedIsTrue : unresolvedDesignMappingPermitted ≡ true
    sampleSizeAndAnalysisNRetained : Bool
    sampleSizeAndAnalysisNRetainedIsTrue :
      sampleSizeAndAnalysisNRetained ≡ true
    unreportedSampleSizeHasNoFabricatedNat : Bool
    unreportedSampleSizeHasNoFabricatedNatIsTrue :
      unreportedSampleSizeHasNoFabricatedNat ≡ true
    uncertaintyAndIntervalSemanticsRetained : Bool
    uncertaintyAndIntervalSemanticsRetainedIsTrue :
      uncertaintyAndIntervalSemanticsRetained ≡ true
    designAndComparatorRetained : Bool
    designAndComparatorRetainedIsTrue : designAndComparatorRetained ≡ true
    attritionMissingnessRetained : Bool
    attritionMissingnessRetainedIsTrue : attritionMissingnessRetained ≡ true
    effectSizeAndMultiplicityRetained : Bool
    effectSizeAndMultiplicityRetainedIsTrue :
      effectSizeAndMultiplicityRetained ≡ true
    populationTimeAndTransportRetained : Bool
    populationTimeAndTransportRetainedIsTrue :
      populationTimeAndTransportRetained ≡ true
    participantRoleRetained : Bool
    participantRoleRetainedIsTrue : participantRoleRetained ≡ true
    claimStrengthBoundedByDesignAndReceipts : Bool
    claimStrengthBoundedByDesignAndReceiptsIsTrue :
      claimStrengthBoundedByDesignAndReceipts ≡ true
    missingQuantitiesMayBeInvented : Bool
    missingQuantitiesMayBeInventedIsFalse : missingQuantitiesMayBeInvented ≡ false
    oneStudyMayClosePopulationCausalMechanismAndPolicyAtOnce : Bool
    oneStudyMayClosePopulationCausalMechanismAndPolicyAtOnceIsFalse :
      oneStudyMayClosePopulationCausalMechanismAndPolicyAtOnce ≡ false

open StudyClaimCeilingBoundary public

canonicalStudyClaimCeilingBoundary : StudyClaimCeilingBoundary
canonicalStudyClaimCeilingBoundary =
  study-claim-ceiling-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl

studyClaimCeilingReading : String
studyClaimCeilingReading =
  "Each admitted digital-ESD paper is indexed by its exact AttributedSource object and interpreted through a design-relative claim ceiling. The source-reported study design is retained verbatim; if the generic design ontology has no exact constructor, mapping remains explicitly unresolved rather than forcing the source into a nearby design class. Source role/locator, source population, reported/enrolled n, analysis n, allocation, comparator, measurement validity, attrition/missingness, confounding control, implementation fidelity, multiplicity, effect-size surface, uncertainty/confidence-interval semantics, time horizon, external-validity domain, participant role and the strongest supported implication are retained separately. Reported and same-object-derived sample sizes carry Nat values; an unreported sample size has no fabricated Nat payload. Reported p-values, large n, narrow confidence intervals, statistical significance, qualitative richness or a positive study finding do not independently manufacture causal identification, representativeness, mechanism, practical significance, population transport, practice recommendation or system transformation. Unreported numerical/statistical quantities remain unreported unless a same-object derivation receipt pays them."
