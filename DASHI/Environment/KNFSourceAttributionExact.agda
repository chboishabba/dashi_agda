module DASHI.Environment.KNFSourceAttributionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Environment.KoreanNaturalFarmingExact as KNF
import DASHI.Environment.SustainableAgricultureManagementSourceRegistryExact as Sources

------------------------------------------------------------------------
-- KNF CLAIM OWNERSHIP / SOURCE ATTRIBUTION
--
-- Repository policy:
-- external source claim != DASHI reconstruction != cross-source inference
-- != DASHI theorem != promoted recommendation.
------------------------------------------------------------------------

data KNFClaimKind : Set where
  practiceLineageClaim
  preparationDescriptionClaim
  applicationDescriptionClaim
  localInputAccountingClaim
  soilMechanismClaim
  microbialOutcomeClaim
  nutrientOutcomeClaim
  cropOutcomeClaim
  causalEffectClaim
  recommendationClaim : KNFClaimKind

record KNFAttributedClaim : Set where
  constructor knf-attributed-claim
  field
    claimKind : KNFClaimKind
    stage : Sources.ClaimStage
    owner : String
    sourceLocator : String
    boundedProposition : String
    excludedInference : String

open KNFAttributedClaim public

knfPracticeLineage : KNFAttributedClaim
knfPracticeLineage = knf-attributed-claim
  practiceLineageClaim
  Sources.externalSourceClaim
  "Han Kyu Cho / Atsushi Koyama; University of Hawai'i CTAHR extension/research lineage"
  "See DASHI.Environment.KoreanNaturalFarmingExact source header and associated source materials"
  "KNF is represented as a practice family including locally prepared biological/mineral/herbal inputs and indigenous-microorganism practice."
  "Does not establish universal mechanism, agronomic benefit, safety, causal effect or recommendation."

imoPreparationDescription : KNFAttributedClaim
imoPreparationDescription = knf-attributed-claim
  preparationDescriptionClaim
  Sources.externalSourceClaim
  "KNF source lineage"
  "canonicalIMO source provenance in KoreanNaturalFarmingExact"
  "The repository source calibration represents IMO through collection/preservation/propagation before situated application."
  "Does not establish that collected organisms are beneficial, mycorrhizal, pathogen-free, or effective at the target site."

knfTypedPracticeSurface : KNFAttributedClaim
knfTypedPracticeSurface = knf-attributed-claim
  applicationDescriptionClaim
  Sources.dashiReconstruction
  "DASHI"
  "DASHI.Environment.KoreanNaturalFarmingExact"
  "KNFPreparation, KNFApplication, KNFOutcomeEvidence and resource-footprint datatypes reconstruct practice, context and evidence as separate coordinates."
  "The external KNF authors are not attributed with these Agda datatypes or repository non-implication theorems."

knfPermacultureCrossPollination : KNFAttributedClaim
knfPermacultureCrossPollination = knf-attributed-claim
  localInputAccountingClaim
  Sources.dashiCrossSourceInference
  "DASHI"
  "DASHI.Environment.KNFPermacultureEmbodiedEnergyBridgeExact"
  "KNF local-input provenance can be compared with permaculture retained-flow/landscape accounting when an explicit same-object resource receipt is supplied."
  "Neither KNF sources nor Holmgren are attributed with DASHI's cross-source resource-flow theorem."

knfSoilPlantFruitChain : KNFAttributedClaim
knfSoilPlantFruitChain = knf-attributed-claim
  soilMechanismClaim
  Sources.dashiCrossSourceInference
  "DASHI"
  "DASHI.Environment.KNFSoilMicrobePlantFruitResourceLoopExact"
  "DASHI factors possible KNF effects through soil process, nutrient, root acquisition, plant allocation and fruit-resource coordinates."
  "Does not assert that KNF pays any edge without application-specific evidence."

knfSituatedNonFactorability : KNFAttributedClaim
knfSituatedNonFactorability = knf-attributed-claim
  cropOutcomeClaim
  Sources.dashiTheorem
  "DASHI"
  "DASHI.Environment.KNFSituatedSiteResponseFibreExact"
  "The finite witness shows that practice identity and anonymous visible reading are insufficient to recover site-conditioned downstream response."
  "The theorem is repo-native and is not an empirical estimate of KNF effect size or a causal attribution to site."

record KNFExperimentalEffectReceipt : Set where
  constructor knf-experimental-effect-receipt
  field
    application : KNF.KNFApplication
    estimandReference : String
    designReference : String
    identificationAssumptionsReference : String
    statisticalRealizationReference : String
    resultReference : String
    externalOrRepositoryOwner : String

open KNFExperimentalEffectReceipt public

record KNFRecommendationReceipt : Set where
  constructor knf-recommendation-receipt
  field
    effect : KNFExperimentalEffectReceipt
    targetSiteReference : String
    transferEvidenceReference : String
    biosecurityReference : String
    safetyReference : String
    resourceCostReference : String
    decisionObjectiveReference : String

open KNFRecommendationReceipt public

data SourceClaimMeansDASHITheoremPermission : Set where

data DashiTheoremMeansEmpiricalEffectPermission : Set where

data ExperimentalEffectMeansRecommendationPermission : Set where

data ExtensionGuidanceMeansUniversalEffectPermission : Set where

sourceClaimDoesNotBecomeDashiTheorem : SourceClaimMeansDASHITheoremPermission → ⊥
sourceClaimDoesNotBecomeDashiTheorem ()

dashiTheoremDoesNotBecomeEmpiricalEffect : DashiTheoremMeansEmpiricalEffectPermission → ⊥
dashiTheoremDoesNotBecomeEmpiricalEffect ()

identifiedEffectDoesNotAutomaticallyPromoteRecommendation : ExperimentalEffectMeansRecommendationPermission → ⊥
identifiedEffectDoesNotAutomaticallyPromoteRecommendation ()

extensionGuidanceDoesNotEstablishUniversalEffect : ExtensionGuidanceMeansUniversalEffectPermission → ⊥
extensionGuidanceDoesNotEstablishUniversalEffect ()

record KNFAttributionBoundary : Set where
  constructor knf-attribution-boundary
  field
    externalPracticeAndDashiFormalisationDistinct : Bool
    crossSourceInferenceIsDashiOwned : Bool
    finiteNonFactorabilityIsDashiTheorem : Bool
    empiricalEffectNeedsSeparateIdentificationReceipt : Bool
    recommendationNeedsSeparatePromotionReceipt : Bool

canonicalKNFAttributionBoundary : KNFAttributionBoundary
canonicalKNFAttributionBoundary =
  knf-attribution-boundary true true true true true
