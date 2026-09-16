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

data DesignReceiptStatus : Set where
  canonicalDesignReceipt : Design.StudyDesignReceipt → DesignReceiptStatus
  sourceReportedDesignUnmapped : String → String → DesignReceiptStatus

data EpistemicRoleStatus : Set where
  reportedEpistemicRole : Design.EpistemicRole → String → EpistemicRoleStatus
  epistemicRoleNotApplicable : String → EpistemicRoleStatus
  epistemicRoleUnresolved : String → EpistemicRoleStatus

data AdmissibleClaimKind : Set where
  implicationConeClaim : Cone.ImplicationKind → AdmissibleClaimKind
  livedExperienceClaim : AdmissibleClaimKind
  implementationContextClaim : AdmissibleClaimKind
  reviewSynthesisClaim : AdmissibleClaimKind
  conceptualMechanismClaim : AdmissibleClaimKind
  modelBasedEnvironmentalImpactClaim : AdmissibleClaimKind

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
studyClaimCoordinates = sourcePopulationCoordinate ∷ enrolledOrReportedNCoordinate ∷ analysisNCoordinate ∷ allocationCoordinate ∷ comparatorCoordinate ∷ measurementValidityCoordinate ∷ attritionMissingnessCoordinate ∷ confoundingControlCoordinate ∷ implementationFidelityCoordinate ∷ multiplicityCoordinate ∷ effectSizeCoordinate ∷ uncertaintyIntervalCoordinate ∷ timeHorizonCoordinate ∷ externalValidityCoordinate ∷ participantRoleCoordinate ∷ implicationCeilingCoordinate ∷ []

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
    participantRoleStatus : EpistemicRoleStatus
    strongestSupportedClaim : AdmissibleClaimKind
    strongestSupportedClaimReference : String
    explicitLimitationsReference : String
open StudyClaimProfile public

designBoundary : Design.EvidenceDesignBoundary
designBoundary = Design.canonicalEvidenceDesignBoundary
implicationConeBoundary : Cone.ExperimentalAssertionConeBoundary
implicationConeBoundary = Cone.canonicalExperimentalAssertionConeBoundary
statisticalBoundary : Statistical.CausalEstimandStatisticalRealisationBoundary
statisticalBoundary = Statistical.canonicalCausalEstimandStatisticalRealisationBoundary
guaranteeBoundary : Guarantees.CausalEstimatorGuaranteeBoundary
guaranteeBoundary = Guarantees.canonicalCausalEstimatorGuaranteeBoundary

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
data NonApplicableParticipantRoleMayBeInvented : Set where
data ModelUncertaintyIntervalCreatesDeploymentMeasurement : Set where

reportedPValueDoesNotCreateCausalIdentification : ReportedPValueCreatesCausalIdentification → ⊥
reportedPValueDoesNotCreateCausalIdentification ()
largeSampleDoesNotCreateRepresentativePopulation : LargeSampleCreatesRepresentativePopulation → ⊥
largeSampleDoesNotCreateRepresentativePopulation ()
confidenceIntervalDoesNotCreatePopulationTransport : ConfidenceIntervalCreatesPopulationTransport → ⊥
confidenceIntervalDoesNotCreatePopulationTransport ()
qualitativeFindingDoesNotCreatePopulationPrevalence : QualitativeFindingCreatesPopulationPrevalence → ⊥
qualitativeFindingDoesNotCreatePopulationPrevalence ()
studyFindingDoesNotCreateSystemTransformation : StudyFindingCreatesSystemTransformation → ⊥
studyFindingDoesNotCreateSystemTransformation ()
missingUncertaintyMayNotBeInvented : MissingUncertaintyMayBeInvented → ⊥
missingUncertaintyMayNotBeInvented ()
narrowIntervalDoesNotCreateMechanismIdentification : NarrowIntervalCreatesMechanismIdentification → ⊥
narrowIntervalDoesNotCreateMechanismIdentification ()
statisticalSignificanceDoesNotCreatePracticalSignificance : StatisticalSignificanceCreatesPracticalSignificance → ⊥
statisticalSignificanceDoesNotCreatePracticalSignificance ()
associationDoesNotCreatePracticeRecommendation : AssociationCreatesPracticeRecommendation → ⊥
associationDoesNotCreatePracticeRecommendation ()
unmappedDesignMayNotBeForcedIntoNearestCanonicalKind : UnmappedDesignMayBeForcedIntoNearestCanonicalKind → ⊥
unmappedDesignMayNotBeForcedIntoNearestCanonicalKind ()
nonApplicableParticipantRoleMayNotBeInvented : NonApplicableParticipantRoleMayBeInvented → ⊥
nonApplicableParticipantRoleMayNotBeInvented ()
modelUncertaintyIntervalDoesNotCreateDeploymentMeasurement :
  ModelUncertaintyIntervalCreatesDeploymentMeasurement → ⊥
modelUncertaintyIntervalDoesNotCreateDeploymentMeasurement ()

record StudyClaimCeilingBoundary : Set where
  constructor study-claim-ceiling-boundary
  field
    attributedSourceObjectRetained : Bool
    attributedSourceObjectRetainedIsTrue : attributedSourceObjectRetained ≡ true
    sourceReportedDesignRetained : Bool
    sourceReportedDesignRetainedIsTrue : sourceReportedDesignRetained ≡ true
    unresolvedDesignMappingPermitted : Bool
    unresolvedDesignMappingPermittedIsTrue : unresolvedDesignMappingPermitted ≡ true
    nonApplicableParticipantRolePermitted : Bool
    nonApplicableParticipantRolePermittedIsTrue : nonApplicableParticipantRolePermitted ≡ true
    qualitativeAndReviewClaimsRemainFirstClass : Bool
    qualitativeAndReviewClaimsRemainFirstClassIsTrue : qualitativeAndReviewClaimsRemainFirstClass ≡ true
    modelBasedLifecycleClaimsRemainFirstClass : Bool
    modelBasedLifecycleClaimsRemainFirstClassIsTrue : modelBasedLifecycleClaimsRemainFirstClass ≡ true
    sampleSizeAndAnalysisNRetained : Bool
    sampleSizeAndAnalysisNRetainedIsTrue : sampleSizeAndAnalysisNRetained ≡ true
    unreportedSampleSizeHasNoFabricatedNat : Bool
    unreportedSampleSizeHasNoFabricatedNatIsTrue : unreportedSampleSizeHasNoFabricatedNat ≡ true
    uncertaintyAndIntervalSemanticsRetained : Bool
    uncertaintyAndIntervalSemanticsRetainedIsTrue : uncertaintyAndIntervalSemanticsRetained ≡ true
    designAndComparatorRetained : Bool
    designAndComparatorRetainedIsTrue : designAndComparatorRetained ≡ true
    attritionMissingnessRetained : Bool
    attritionMissingnessRetainedIsTrue : attritionMissingnessRetained ≡ true
    effectSizeAndMultiplicityRetained : Bool
    effectSizeAndMultiplicityRetainedIsTrue : effectSizeAndMultiplicityRetained ≡ true
    populationTimeAndTransportRetained : Bool
    populationTimeAndTransportRetainedIsTrue : populationTimeAndTransportRetained ≡ true
    participantRoleRetained : Bool
    participantRoleRetainedIsTrue : participantRoleRetained ≡ true
    claimStrengthBoundedByDesignAndReceipts : Bool
    claimStrengthBoundedByDesignAndReceiptsIsTrue : claimStrengthBoundedByDesignAndReceipts ≡ true
    missingQuantitiesMayBeInvented : Bool
    missingQuantitiesMayBeInventedIsFalse : missingQuantitiesMayBeInvented ≡ false
    oneStudyMayClosePopulationCausalMechanismAndPolicyAtOnce : Bool
    oneStudyMayClosePopulationCausalMechanismAndPolicyAtOnceIsFalse : oneStudyMayClosePopulationCausalMechanismAndPolicyAtOnce ≡ false
open StudyClaimCeilingBoundary public

canonicalStudyClaimCeilingBoundary : StudyClaimCeilingBoundary
canonicalStudyClaimCeilingBoundary = study-claim-ceiling-boundary true refl true refl true refl true refl true refl true refl true refl true refl true refl true refl true refl true refl true refl true refl false refl false refl

studyClaimCeilingReading : String
studyClaimCeilingReading = "Each admitted digital-ESD paper is indexed by its exact AttributedSource object and interpreted through a design-relative claim ceiling. Source-reported design is retained verbatim and may remain unmapped when the canonical design ontology lacks an exact constructor. Participant epistemic role may be source-reported, unresolved or not applicable. Strongest supported claim may be a causal/experimental implication, lived-experience claim, implementation-context claim, review synthesis, conceptual mechanism, or model-based environmental-impact claim, so qualitative, review, conceptual and lifecycle-model evidence are not forced into one causal ladder. Sample sizes, effect/uncertainty surfaces, time, transport and limitations remain source-specific; missing quantities are not invented. A model-based 95% uncertainty interval remains uncertainty about the modelled result and does not create a measured footprint for another deployment."
