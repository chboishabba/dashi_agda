module DASHI.Biology.ChegenWalshUndermethylationAssertionConeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.ChegenWalshUndermethylationSourceAtlasExact as Sources
import DASHI.Biology.OneCarbonHistamineMethylationNetworkExact as Network
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as GenericCone
import DASHI.Biology.CausalIdentificationFamiliesExact as Identification

------------------------------------------------------------------------
-- REEL 19 ASSERTION CONE
--
-- Natural-language claims are separated by speaker/source and then by
-- inferential force.  "The reel says X" is representable even where
-- "X is biologically established" is blocked.
------------------------------------------------------------------------

data ClaimSpeaker : Set where
  chegenCreator : ClaimSpeaker
  walshProgram : ClaimSpeaker
  peerReviewedLiterature : ClaimSpeaker
  dashiSynthesis : ClaimSpeaker

data ClaimKind : Set where
  phenotypeAssociation : ClaimKind
  biochemicalMechanism : ClaimKind
  biomarkerInference : ClaimKind
  diagnosticInference : ClaimKind
  treatmentInference : ClaimKind
  sourceSizeClaim : ClaimKind

data ClaimStatus : Set where
  sourceReportedOnly : ClaimStatus
  externallySupportedBounded : ClaimStatus
  qualified : ClaimStatus
  blocked : ClaimStatus
  openEmpiricalQuestion : ClaimStatus

record AttributedClaim : Set where
  constructor attributedClaim
  field
    key : String
    speaker : ClaimSpeaker
    source : Source.AttributedSource
    kind : ClaimKind
    exactOrBoundedReading : String
    status : ClaimStatus
    statusReference : String

open AttributedClaim public

chegenFingerprintClaim : AttributedClaim
chegenFingerprintClaim =
  attributedClaim
    "chegen-reel19-specific-fingerprint"
    chegenCreator
    Sources.chegenReel19
    phenotypeAssociation
    "The reel states that 'undermethylation' has a specific fingerprint including high achievement drive, chronic anxiety, obsessive/looping thoughts, competitiveness, poor stress recovery, seasonal allergies/histamine reactivity, OCD/perfectionism/addiction history, sparse body hair, low pain tolerance, and cold hands/feet."
    sourceReportedOnly
    "Attributed to @danielchegenp from the user-supplied Reel 19 transcript; not promoted as a validated diagnostic phenotype."

chegenSingleRouteClaim : AttributedClaim
chegenSingleRouteClaim =
  attributedClaim
    "chegen-reel19-one-biochemical-route"
    chegenCreator
    Sources.chegenReel19
    biochemicalMechanism
    "The reel states that these features share one biochemical route involving serotonin production, neurotransmitter synthesis, histamine clearance, and epigenetic regulation."
    qualified
    "One-carbon/SAM chemistry genuinely touches HNMT, COMT and DNMT-like methyltransferases, but the repo network keeps their pathways and substrates distinct; shared SAM dependence does not identify one mechanism."

chegenCapsuleClaim : AttributedClaim
chegenCapsuleClaim =
  attributedClaim
    "chegen-reel19-single-capsule"
    chegenCreator
    Sources.chegenReel19
    treatmentInference
    "The reel previews a subsequent 'single capsule' intended to address the assembled MTHFR/histamine/COMT framework."
    blocked
    "A social-media treatment framing does not provide intervention efficacy, safety, subgroup identification, dose-response, or comparative-treatment receipts."

walshThirtyThousandClaim : AttributedClaim
walshThirtyThousandClaim =
  attributedClaim
    "walsh-thirty-thousand-evaluated"
    walshProgram
    Sources.walshInterviewThirtyThousand
    sourceSizeClaim
    "Walsh states that he evaluated approximately 30,000 patients with respect to methylation over decades of clinical work."
    sourceReportedOnly
    "The source supports the historical practitioner-database claim; it is not by itself a prospective, population-representative, blinded, or independently replicated validation study."

mthfrOneCarbonClaim : AttributedClaim
mthfrOneCarbonClaim =
  attributedClaim
    "mthfr-one-carbon-role"
    peerReviewedLiterature
    Sources.mthfrPerspective2026
    biochemicalMechanism
    "MTHFR reduces 5,10-methylene-THF to 5-methyl-THF and helps direct one-carbon units toward methionine-cycle methyl-donor metabolism."
    externallySupportedBounded
    "Peer-reviewed biochemical review."

samMultipleMethyltransferasesClaim : AttributedClaim
samMultipleMethyltransferasesClaim =
  attributedClaim
    "sam-shared-methyl-donor"
    peerReviewedLiterature
    Sources.samMethyltransferases2021
    biochemicalMechanism
    "SAM serves as a methyl donor for multiple distinct methyltransferases including HNMT, COMT and DNMT-family enzymes."
    externallySupportedBounded
    "Peer-reviewed review; source supports common methyl-donor chemistry but not a unitary clinical phenotype."

canonicalReel19Claims : List AttributedClaim
canonicalReel19Claims =
  chegenFingerprintClaim
  ∷ chegenSingleRouteClaim
  ∷ chegenCapsuleClaim
  ∷ walshThirtyThousandClaim
  ∷ mthfrOneCarbonClaim
  ∷ samMultipleMethyltransferasesClaim
  ∷ []

------------------------------------------------------------------------
-- Promotion gates for the reel's implied chain.
------------------------------------------------------------------------

data PromotionEdge : Set where
  traitsToBiochemicalState : PromotionEdge
  bloodHistamineToGlobalMethylation : PromotionEdge
  mthfrVariantToWalshSubtype : PromotionEdge
  sharedSAMToSingleMechanism : PromotionEdge
  biochemicalStateToDiagnosis : PromotionEdge
  phenotypeToSupplementRecommendation : PromotionEdge

record PromotionAssessment : Set where
  constructor promotionAssessment
  field
    edge : PromotionEdge
    status : ClaimStatus
    reason : String

open PromotionAssessment public

traitsToBiochemicalStateAssessment : PromotionAssessment
traitsToBiochemicalStateAssessment =
  promotionAssessment traitsToBiochemicalState blocked
    "Trait clustering alone does not identify a unique one-carbon, methyltransferase, histamine, or epigenetic state."

bloodHistamineAssessment : PromotionAssessment
bloodHistamineAssessment =
  promotionAssessment bloodHistamineToGlobalMethylation openEmpiricalQuestion
    "Whole-blood histamine may be an observable relevant to histamine biology, but a calibrated transport from that assay to global methylation capacity requires an independent validation receipt."

mthfrSubtypeAssessment : PromotionAssessment
mthfrSubtypeAssessment =
  promotionAssessment mthfrVariantToWalshSubtype blocked
    "A common MTHFR genotype does not definitionally establish the Walsh-labelled subtype."

sharedSAMAssessment : PromotionAssessment
sharedSAMAssessment =
  promotionAssessment sharedSAMToSingleMechanism blocked
    "HNMT, COMT and DNMT can share SAM while remaining distinct enzymes, substrates, tissues and physiological processes."

diagnosisAssessment : PromotionAssessment
diagnosisAssessment =
  promotionAssessment biochemicalStateToDiagnosis blocked
    "No diagnostic authority is imported by the source atlas or biochemical network."

supplementAssessment : PromotionAssessment
supplementAssessment =
  promotionAssessment phenotypeToSupplementRecommendation blocked
    "Treatment recommendation requires intervention-specific efficacy/safety evidence and a validated target-population bridge."

canonicalPromotionAssessments : List PromotionAssessment
canonicalPromotionAssessments =
  traitsToBiochemicalStateAssessment
  ∷ bloodHistamineAssessment
  ∷ mthfrSubtypeAssessment
  ∷ sharedSAMAssessment
  ∷ diagnosisAssessment
  ∷ supplementAssessment
  ∷ []

------------------------------------------------------------------------
-- Strong attribution theorem: source statements survive criticism intact.
------------------------------------------------------------------------

record AttributionPreservationBoundary : Set where
  constructor attributionPreservationBoundary
  field
    canRecordReelClaimWithoutEndorsingIt : Bool
    canRecordReelClaimWithoutEndorsingItIsTrue :
      canRecordReelClaimWithoutEndorsingIt ≡ true
    canRecordWalshClaimWithoutAttributingItToChegen : Bool
    canRecordWalshClaimWithoutAttributingItToChegenIsTrue :
      canRecordWalshClaimWithoutAttributingItToChegen ≡ true
    canQualifyClaimWithoutErasingSource : Bool
    canQualifyClaimWithoutErasingSourceIsTrue :
      canQualifyClaimWithoutErasingSource ≡ true
    dashiCrossSourceSynthesisIsExternalQuotation : Bool
    dashiCrossSourceSynthesisIsExternalQuotationIsFalse :
      dashiCrossSourceSynthesisIsExternalQuotation ≡ false

canonicalAttributionPreservationBoundary :
  AttributionPreservationBoundary
canonicalAttributionPreservationBoundary =
  attributionPreservationBoundary
    true refl
    true refl
    true refl
    false refl

------------------------------------------------------------------------
-- Projection into the repo-generic implication-cone / causal-ID machinery.
--
-- The domain owner retains sourceReportedOnly/openEmpiricalQuestion because
-- those carry useful provenance states not present in the three-valued generic
-- cone.  Promotion-relevant readings project into the canonical cone rather
-- than creating a second implication semantics.
------------------------------------------------------------------------

toGenericConeStatus : ClaimStatus → GenericCone.ConeEdgeStatus
toGenericConeStatus sourceReportedOnly = GenericCone.qualifiedEdge
toGenericConeStatus externallySupportedBounded = GenericCone.supportedEdge
toGenericConeStatus qualified = GenericCone.qualifiedEdge
toGenericConeStatus blocked = GenericCone.blockedEdge
toGenericConeStatus openEmpiricalQuestion = GenericCone.qualifiedEdge

data ReelImplicationClass : Set where
  measuredOrReportedResultClass : ReelImplicationClass
  associationClass : ReelImplicationClass
  causalEffectClass : ReelImplicationClass
  mechanismClass : ReelImplicationClass
  practiceRecommendationClass : ReelImplicationClass

toGenericImplicationKind : ReelImplicationClass → GenericCone.ImplicationKind
toGenericImplicationKind measuredOrReportedResultClass =
  GenericCone.restatesMeasuredResult
toGenericImplicationKind associationClass =
  GenericCone.associatesTreatmentAndOutcome
toGenericImplicationKind causalEffectClass =
  GenericCone.attributesCausalEffect
toGenericImplicationKind mechanismClass =
  GenericCone.identifiesMechanism
toGenericImplicationKind practiceRecommendationClass =
  GenericCone.recommendsPractice

canonicalIdentificationFamiliesRequired :
  List Identification.CausalIdentificationFamily
canonicalIdentificationFamiliesRequired =
  Identification.adjustedObservationalComparison
  ∷ Identification.mechanisticMediation
  ∷ []

record ExistingMachineryCrossPollination : Set where
  constructor existingMachineryCrossPollination
  field
    genericConeOwner : String
    causalIdentificationOwner : String
    sourceAtlasOwner : String
    networkOwner : String
    reading : String

canonicalExistingMachineryCrossPollination :
  ExistingMachineryCrossPollination
canonicalExistingMachineryCrossPollination =
  existingMachineryCrossPollination
    "DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact"
    "DASHI.Biology.CausalIdentificationFamiliesExact"
    "DASHI.Biology.ChegenWalshUndermethylationSourceAtlasExact"
    "DASHI.Biology.OneCarbonHistamineMethylationNetworkExact"
    "Reel-specific source states project into the existing generic implication cone; any promotion from association to causal mechanism requires obligation-relative causal-identification receipts rather than a domain-local shortcut."
