module DASHI.Environment.KNFSourceAttributionLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Environment.KoreanNaturalFarmingExact as KNF
import DASHI.Environment.LESObservationSourceRegistryExact as LESSources
import DASHI.Environment.KNFPermacultureEmbodiedEnergyBridgeExact as KNFPermaculture
import DASHI.Environment.KNFSoilMicrobePlantFruitResourceLoopExact as ResourceLoop
import DASHI.Environment.KNFPlantSoilReturnFlowLoopExact as ReturnLoop
import DASHI.Environment.KNFSituatedSiteResponseFibreExact as Situated

------------------------------------------------------------------------
-- KNF / PERMACULTURE SOURCE ATTRIBUTION LINEAGE
--
-- Repository policy projection:
--
--   external source claim / datum
--      != DASHI formal reconstruction
--      != DASHI cross-source / cross-module inference
--      != new DASHI theorem / extension
--      != promotion or external adjudication.
--
-- This module is a KNF-specific specialization of that policy.  It reuses the
-- repository ScientificWorkAttribution owner for person/work/claim ownership;
-- it does not create a competing generic provenance architecture.
------------------------------------------------------------------------

data KNFClaimStage : Set where
  externalSourceClaim
  dashiFormalReconstruction
  dashiCrossSourceInference
  dashiExtensionTheorem
  promotionOrExternalAdjudication : KNFClaimStage

data KNFSourceRole : Set where
  practiceLineageSource
  extensionPracticeSource
  permacultureDesignCalibration
  empiricalOutcomeSource
  repositoryTypedOwner : KNFSourceRole

record KNFClaimAttribution : Set where
  constructor knf-claim-attribution
  field
    claimId : String
    claimReading : String
    stage : KNFClaimStage
    sourceRole : KNFSourceRole
    sourceLocator : String
    stableIdentifier : String
    claimScope : String
    excludedReading : String
    claimOwner : Attribution.ClaimOwner

open KNFClaimAttribution public

------------------------------------------------------------------------
-- Person/work receipts use the canonical non-laundering owner.
--
-- The repository KNF module currently records Cho & Koyama (1997) as the
-- source lineage for Korean Natural Farming.  Stronger identifier metadata is
-- not invented here: source attribution policy explicitly prefers an accurate
-- recoverable attribution over a fabricated DOI/ISBN.
------------------------------------------------------------------------

choPracticeAttribution : Attribution.ScientificWorkAttribution
choPracticeAttribution =
  Attribution.scientific-work-attribution
    "Han Kyu Cho"
    "Korean Natural Farming"
    "KNF practice lineage recorded by DASHI.Environment.KoreanNaturalFarmingExact"
    Attribution.namedAuthor
    Attribution.primaryPublicationRecord
    "Cho / Koyama, Korean Natural Farming (1997); consult source bibliography for stronger identifier"
    "Named source author for the KNF practice lineage; not owner of DASHI soil, fibre, causal, or resource-loop theorems."
    Attribution.externalSourceOwner

koyamaPracticeAttribution : Attribution.ScientificWorkAttribution
koyamaPracticeAttribution =
  Attribution.scientific-work-attribution
    "Atsushi Koyama"
    "Korean Natural Farming"
    "KNF practice lineage recorded by DASHI.Environment.KoreanNaturalFarmingExact"
    Attribution.namedAuthor
    Attribution.primaryPublicationRecord
    "Cho / Koyama, Korean Natural Farming (1997); consult source bibliography for stronger identifier"
    "Named source author for the KNF practice lineage; not owner of DASHI soil, fibre, causal, or resource-loop theorems."
    Attribution.externalSourceOwner

------------------------------------------------------------------------
-- Claim-specific receipts.
------------------------------------------------------------------------

choKoyamaPracticeLineage : KNFClaimAttribution
choKoyamaPracticeLineage =
  knf-claim-attribution
    "knf-practice-lineage"
    "Korean Natural Farming is represented here as a source-attributed practice family with preparations, processes, application targets and context."
    externalSourceClaim
    practiceLineageSource
    "Cho / Koyama, Korean Natural Farming (1997), as recorded in DASHI.Environment.KoreanNaturalFarmingExact"
    "Stronger stable identifier not verified in this repository lane"
    "Practice lineage / methodology only"
    "Does not establish universal soil, yield, plant-health, pest, safety, sustainability, or causal-effect claims and does not state DASHI formal types."
    Attribution.externalSourceOwner

uhExtensionPracticeLineage : KNFClaimAttribution
uhExtensionPracticeLineage =
  knf-claim-attribution
    "knf-uh-extension-practice"
    "University of Hawai'i CTAHR KNF/IMO materials are used as extension/practice calibration for local microorganism collection, preparation and application context."
    externalSourceClaim
    extensionPracticeSource
    "University of Hawai'i CTAHR KNF/IMO extension materials, as recorded in DASHI.Environment.KoreanNaturalFarmingExact"
    "Institutional source locator retained; stronger publication identifier must be supplied claim-by-claim when verified"
    "Extension/practice description"
    "Extension guidance is not automatically a controlled trial, replicated effect, causal identification, safety finding, or universal recommendation."
    Attribution.externalSourceOwner

holmgrenObservationCalibration : KNFClaimAttribution
holmgrenObservationCalibration =
  knf-claim-attribution
    "permaculture-observe-interact-calibration"
    (LESSources.boundedReading LESSources.holmgren2002)
    externalSourceClaim
    permacultureDesignCalibration
    (LESSources.identifier LESSources.holmgren2002)
    (LESSources.identifier LESSources.holmgren2002)
    "Permaculture Observe and Interact design calibration"
    (LESSources.excludedPromotion LESSources.holmgren2002)
    Attribution.externalSourceOwner

knfFormalPracticeSurface : KNFClaimAttribution
knfFormalPracticeSurface =
  knf-claim-attribution
    "dashi-knf-formal-practice-surface"
    "The KNFPreparation, KNFApplication, KNFOutcomeEvidence and resource-footprint carriers are DASHI formal reconstructions around the attributed practice lineage."
    dashiFormalReconstruction
    repositoryTypedOwner
    "DASHI.Environment.KoreanNaturalFarmingExact"
    "Repository-native typed owner"
    "Formal reconstruction"
    "Must not be reported as Agda mathematics authored by Cho, Koyama, CTAHR, Holmgren, or an empirical trial."
    Attribution.dashiFormalisationOwner

knfPermacultureCrossSourceBridge : KNFClaimAttribution
knfPermacultureCrossSourceBridge =
  knf-claim-attribution
    "dashi-knf-permaculture-cross-source-bridge"
    "Mapping KNF local-flow transformations into permaculture embodied-energy / retained-flow accounting is a DASHI cross-source and cross-module inference."
    dashiCrossSourceInference
    repositoryTypedOwner
    "DASHI.Environment.KNFPermacultureEmbodiedEnergyBridgeExact"
    "Repository-native typed owner"
    "Cross-source structural inference"
    "Neither the KNF source lineage nor Holmgren is attributed with stating this DASHI bridge or its same-object receipts."
    Attribution.dashiInferenceOwner

soilPlantFruitResourceLoopReconstruction : KNFClaimAttribution
soilPlantFruitResourceLoopReconstruction =
  knf-claim-attribution
    "dashi-knf-soil-plant-fruit-resource-loop"
    "The practice -> soil process -> root acquisition -> plant allocation -> fruit investment chain is a DASHI reconstruction requiring evidence or same-object receipts at every cross-domain arrow."
    dashiFormalReconstruction
    repositoryTypedOwner
    "DASHI.Environment.KNFSoilMicrobePlantFruitResourceLoopExact"
    "Repository-native typed owner"
    "Cross-domain structural reconstruction"
    "Does not assert that a KNF application causes microbiome, nutrient, uptake, fruit, repair, yield, or fitness improvement."
    Attribution.dashiFormalisationOwner

plantSoilReturnLoopReconstruction : KNFClaimAttribution
plantSoilReturnLoopReconstruction =
  knf-claim-attribution
    "dashi-plant-soil-return-loop"
    "Root exudation, turnover, litter, fruit/pruning residue and fungal carbon-transfer channels are represented as candidate return paths into the existing soil C/N network."
    dashiFormalReconstruction
    repositoryTypedOwner
    "DASHI.Environment.KNFPlantSoilReturnFlowLoopExact"
    "Repository-native typed owner"
    "Return-flow structural reconstruction"
    "Does not claim every channel is active, beneficial, quantitatively closed, lossless, or empirically established at every site."
    Attribution.dashiFormalisationOwner

situatedResponseNonFactorabilityTheorem : KNFClaimAttribution
situatedResponseNonFactorabilityTheorem =
  knf-claim-attribution
    "dashi-knf-situated-response-nonfactorability"
    "The finite same-practice / different-context response collision is a repository-native DASHI non-factorability theorem."
    dashiExtensionTheorem
    repositoryTypedOwner
    "DASHI.Environment.KNFSituatedSiteResponseFibreExact"
    "Repository-native typed theorem"
    "Finite formal witness"
    "It does not identify a causal KNF effect, estimate an effect size, prove site causation, or establish portability."
    Attribution.dashiInferenceOwner

------------------------------------------------------------------------
-- Claim-stage / owner consistency.
------------------------------------------------------------------------

stageOwnerExpected : KNFClaimStage → Attribution.ClaimOwner
stageOwnerExpected externalSourceClaim = Attribution.externalSourceOwner
stageOwnerExpected dashiFormalReconstruction = Attribution.dashiFormalisationOwner
stageOwnerExpected dashiCrossSourceInference = Attribution.dashiInferenceOwner
stageOwnerExpected dashiExtensionTheorem = Attribution.dashiInferenceOwner
stageOwnerExpected promotionOrExternalAdjudication = Attribution.unresolvedClaimOwner

record AttributionConsistent (a : KNFClaimAttribution) : Set where
  constructor attribution-consistent
  field
    ownerMatchesStage : claimOwner a ≡ stageOwnerExpected (stage a)

open AttributionConsistent public

choKoyamaPracticeLineageConsistent : AttributionConsistent choKoyamaPracticeLineage
choKoyamaPracticeLineageConsistent = attribution-consistent refl

knfFormalPracticeSurfaceConsistent : AttributionConsistent knfFormalPracticeSurface
knfFormalPracticeSurfaceConsistent = attribution-consistent refl

knfPermacultureCrossSourceBridgeConsistent : AttributionConsistent knfPermacultureCrossSourceBridge
knfPermacultureCrossSourceBridgeConsistent = attribution-consistent refl

situatedResponseTheoremConsistent : AttributionConsistent situatedResponseNonFactorabilityTheorem
situatedResponseTheoremConsistent = attribution-consistent refl

------------------------------------------------------------------------
-- Promotion and attribution firewalls.
------------------------------------------------------------------------

data CitationMeansTruthPermission : Set where

data SourceDescriptionMeansOutcomeProofPermission : Set where

data ExtensionGuidanceMeansControlledTrialPermission : Set where

data SourceAttributionMeansEndorsementPermission : Set where

data FormalisationTransfersAuthorshipPermission : Set where

data CrossSourceBridgeWasStatedByEitherSourcePermission : Set where

data SiteSpecificStudyMeansUniversalEffectPermission : Set where

data FormalNonFactorabilityMeansCausalIdentificationPermission : Set where

data LocalNaturalMeansSafeOrAuthorizedPermission : Set where

data EvidenceMeansRecommendationPromotionPermission : Set where

citationDoesNotByItselfProveTruth : CitationMeansTruthPermission → ⊥
citationDoesNotByItselfProveTruth ()

sourceDescriptionDoesNotByItselfProveOutcome :
  SourceDescriptionMeansOutcomeProofPermission → ⊥
sourceDescriptionDoesNotByItselfProveOutcome ()

extensionGuidanceIsNotDefinitionallyControlledTrial :
  ExtensionGuidanceMeansControlledTrialPermission → ⊥
extensionGuidanceIsNotDefinitionallyControlledTrial ()

sourceAttributionIsNotEndorsement : SourceAttributionMeansEndorsementPermission → ⊥
sourceAttributionIsNotEndorsement ()

formalisationDoesNotTransferExternalAuthorship :
  FormalisationTransfersAuthorshipPermission → ⊥
formalisationDoesNotTransferExternalAuthorship ()

crossSourceBridgeIsNotAttributedBackToEitherSource :
  CrossSourceBridgeWasStatedByEitherSourcePermission → ⊥
crossSourceBridgeIsNotAttributedBackToEitherSource ()

siteSpecificStudyDoesNotEstablishUniversalEffect :
  SiteSpecificStudyMeansUniversalEffectPermission → ⊥
siteSpecificStudyDoesNotEstablishUniversalEffect ()

formalNonFactorabilityDoesNotIdentifyCausalEffect :
  FormalNonFactorabilityMeansCausalIdentificationPermission → ⊥
formalNonFactorabilityDoesNotIdentifyCausalEffect ()

localOrNaturalDoesNotEstablishSafetyOrAuthorization :
  LocalNaturalMeansSafeOrAuthorizedPermission → ⊥
localOrNaturalDoesNotEstablishSafetyOrAuthorization ()

evidenceDoesNotAutomaticallyPromoteRecommendation :
  EvidenceMeansRecommendationPromotionPermission → ⊥
evidenceDoesNotAutomaticallyPromoteRecommendation ()

record KNFSourceAttributionBoundary : Set where
  constructor knf-source-attribution-boundary
  field
    externalPracticeLineageIsRecorded : Bool
    stableIdentifierMustNotBeFabricated : Bool
    sourceClaimAndDashiReconstructionAreDistinct : Bool
    crossSourceInferenceHasDashiOwner : Bool
    dashiTheoremIsNotAttributedToExternalAuthor : Bool
    extensionGuidanceIsNotControlledTrial : Bool
    formalNonFactorabilityIsNotCausalIdentification : Bool
    empiricalEvidenceAutomaticallyPromotesRecommendation : Bool

canonicalKNFSourceAttributionBoundary : KNFSourceAttributionBoundary
canonicalKNFSourceAttributionBoundary =
  knf-source-attribution-boundary
    true true true true true true true false
