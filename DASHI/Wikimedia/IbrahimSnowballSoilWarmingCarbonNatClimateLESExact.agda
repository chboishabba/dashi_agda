module DASHI.Wikimedia.IbrahimSnowballSoilWarmingCarbonNatClimateLESExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballDecompositionMicrobialRhizosphereMycorrhizaLESExact as SoilBiology
import DASHI.Wikimedia.IbrahimSnowballEcologyEcosystemBiogeochemistryLESExact as Ecology
import DASHI.Wikimedia.SensibLawNatClimateReviewHandoffExact as NatClimate
import DASHI.Wikimedia.SensibLawNatObservationClaimSLRExact as NatObservation

------------------------------------------------------------------------
-- IBRAHIM / LES SOIL-BIOLOGY -> CLIMATE SNOWBALL
--
-- decomposition / microbes / rhizosphere / mycorrhiza
--      <-> soil carbon / respiration / mineral N
--      <-> warming intervention / ecosystem carbon flux
--      <-> climate-change and emissions accounting consumers
--
-- QIDs are identity/navigation coordinates only.  Nat-climate P5991/P14143
-- migration remains statement-bundle/review dependent.  Local ecological CO2
-- flux, soil-carbon stock, entity carbon footprint and annual entity GHG
-- emissions remain different consumers.
------------------------------------------------------------------------

climateChangeQid : Identity.ExternalIdentityDemand
climateChangeQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES soil-climate continuation" "external climate concept identity"
  "climate change" Identity.wikidataQid
  (Identity.verified "Q125928" "Wikidata climate-change identity checked 2026-09-10")

soilCarbonQid : Identity.ExternalIdentityDemand
soilCarbonQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES soil-climate continuation" "external soil-carbon identity"
  "soil carbon" Identity.wikidataQid
  (Identity.verified "Q7554898" "Wikidata soil-carbon identity checked 2026-09-10")

carbonFootprintQid : Identity.ExternalIdentityDemand
carbonFootprintQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES soil-climate continuation" "external accounting-concept identity"
  "carbon footprint" Identity.wikidataQid
  (Identity.verified "Q310667" "Wikidata carbon-footprint identity checked 2026-09-10")

greenhouseGasEmissionsQid : Identity.ExternalIdentityDemand
greenhouseGasEmissionsQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES soil-climate continuation" "external emissions-concept identity"
  "greenhouse gas emissions" Identity.wikidataQid
  (Identity.verified "Q106358009" "Wikidata GHG-emissions identity checked 2026-09-10")

------------------------------------------------------------------------
-- Primary source carriers: warming experiments, not global attribution claims.
------------------------------------------------------------------------

data SoilClimateSourceRole : Set where
  decadeSoilWarmingExperiment
  longTermSoilWarmingExperiment
  deepSoilWarmingExperiment : SoilClimateSourceRole

record SoilClimatePrimarySource : Set where
  constructor soil-climate-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    role : SoilClimateSourceRole
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open SoilClimatePrimarySource public

melillo2002 : SoilClimatePrimarySource
melillo2002 = soil-climate-primary-source
  "J. M. Melillo; P. A. Steudler; J. D. Aber; K. Newkirk; H. Lux; F. P. Bowles; C. Catricala; A. Magill; T. Ahrens; S. Morrisseau"
  "Soil warming and carbon-cycle feedbacks to the climate system"
  "Science 298(5601):2173-2176"
  2002
  "DOI 10.1126/science.1074153; PMID 12481133"
  decadeSoilWarmingExperiment
  "Primary decade-scale mid-latitude hardwood-forest warming experiment measuring soil C/N cycling, soil CO2 flux and mineral-N availability responses."
  "Does not establish universal soil-carbon sensitivity, global climate attribution, annual entity GHG emissions, carbon footprint, or universal plant benefit."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

melillo2017 : SoilClimatePrimarySource
melillo2017 = soil-climate-primary-source
  "J. M. Melillo; S. D. Frey; K. M. DeAngelis; W. J. Werner; M. J. Bernard; F. P. Bowles; G. Pold; M. A. Knorr; A. S. Grandy"
  "Long-term pattern and magnitude of soil carbon feedback to the climate system in a warming world"
  "Science 358(6359):101-105"
  2017
  "DOI 10.1126/science.aan2874; PMID 28983050"
  longTermSoilWarmingExperiment
  "Primary 26-year soil-warming experiment showing multi-phase soil-organic-matter decay and CO2-flux response with microbial biomass/community and carbon-use-efficiency changes."
  "Does not make every ecosystem follow the same temporal phases and does not identify entity-level emissions or footprint accounting."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

hicksPries2017 : SoilClimatePrimarySource
hicksPries2017 = soil-climate-primary-source
  "Caitlin E. Hicks Pries; C. Castanha; R. C. Porras; M. S. Torn"
  "The whole-soil carbon flux in response to warming"
  "Science 355(6332):1420-1423"
  2017
  "DOI 10.1126/science.aal1319; PMID 28280251"
  deepSoilWarmingExperiment
  "Primary in-situ deep mineral-soil warming experiment measuring CO2 production across soil depths under a +4 C treatment."
  "Does not identify all emitted CO2 as anthropogenic annual GHG emissions and does not by itself close whole-ecosystem carbon budgets."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

record SoilClimateSourceAdmission : Set where
  constructor soil-climate-source-admission
  field
    source : SoilClimatePrimarySource
    exactExperimentReference : String
    exactSiteReference : String
    exactTreatmentReference : String
    exactResponseReference : String
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner
    dashiCrosswalkOwner : Attribution.ClaimOwner
    dashiOwnsCrosswalkOnly : dashiCrosswalkOwner ≡ Attribution.dashiFormalisationOwner

open SoilClimateSourceAdmission public

------------------------------------------------------------------------
-- Consumer decomposition across ecology and Nat climate accounting.
------------------------------------------------------------------------

data SoilClimateConsumer : Set where
  localSoilCO2Flux
  soilCarbonStock
  mineralNitrogenAvailability
  microbialCommunityResponse
  ecosystemCarbonBalance
  carbonFootprintAccounting
  annualEntityGHGEmissions
  climateChangeAttribution : SoilClimateConsumer

record SoilClimateConsumerBoundary : Set where
  constructor soil-climate-consumer-boundary
  field
    localFluxSeparateFromStock : Bool
    localFluxSeparateFromEntityEmissions : Bool
    soilStockSeparateFromFootprint : Bool
    footprintSeparateFromAnnualGHG : Bool
    annualGHGSeparateFromClimateAttribution : Bool
    warmingExperimentSeparateFromGlobalClimateAttribution : Bool
    NatPropertyMigrationStillReviewDependent : Bool

canonicalSoilClimateConsumerBoundary : SoilClimateConsumerBoundary
canonicalSoilClimateConsumerBoundary =
  soil-climate-consumer-boundary true true true true true true true

------------------------------------------------------------------------
-- Snowball: collect primary ecology and Wikidata/Nat material out of order;
-- payment only advances with exact same-site/boundary/accounting receipts.
------------------------------------------------------------------------

record SoilClimateAcquisitionState : Set where
  constructor soil-climate-acquisition-state
  field
    climateChangeQidAcquired : Bool
    soilCarbonQidAcquired : Bool
    carbonFootprintQidAcquired : Bool
    greenhouseGasEmissionsQidAcquired : Bool
    melillo2002Acquired : Bool
    melillo2017Acquired : Bool
    deepSoilWarmingAcquired : Bool
    soilTemperatureEvidenceAcquired : Bool
    soilMoistureEvidenceAcquired : Bool
    soilCO2FluxEvidenceAcquired : Bool
    soilCarbonStockEvidenceAcquired : Bool
    mineralNitrogenEvidenceAcquired : Bool
    microbialCommunityEvidenceAcquired : Bool
    ecosystemCarbonBudgetEvidenceAcquired : Bool
    NatStatementBundleEvidenceAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open SoilClimateAcquisitionState public

record SoilClimatePaymentState : Set where
  constructor soil-climate-payment-state
  field
    qidIdentityPaid : Bool
    exactPrimarySourcePaid : Bool
    sourceRoleAttributionPaid : Bool
    exactSiteIdentityPaid : Bool
    warmingTreatmentIdentityPaid : Bool
    soilTemperatureBoundaryPaid : Bool
    soilMoistureBoundaryPaid : Bool
    soilCO2FluxPaid : Bool
    soilCarbonStockPaid : Bool
    mineralNitrogenPaid : Bool
    microbialResponsePaid : Bool
    ecosystemCarbonBalancePaid : Bool
    entityAccountingBoundaryPaid : Bool
    p5991P14143StatementBundleReviewPaid : Bool
    climateAttributionPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open SoilClimatePaymentState public

snowballAcquisitionDoesNotAdvanceSoilClimatePayment :
  SoilClimateAcquisitionState → SoilClimatePaymentState → SoilClimatePaymentState
snowballAcquisitionDoesNotAdvanceSoilClimatePayment _ payment = payment

------------------------------------------------------------------------
-- Explicit Nat handoff reuse.
------------------------------------------------------------------------

natClimateBoundary : NatClimate.NatClimateHandoffBoundary
natClimateBoundary = NatClimate.canonicalNatClimateHandoffBoundary

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

------------------------------------------------------------------------
-- WrongType / no-promotion barriers.
------------------------------------------------------------------------

data LocalSoilCO2FluxMeansAnnualEntityGHG : Set where
data SoilCarbonStockMeansCarbonFootprint : Set where
data SoilWarmingResponseMeansClimateAttribution : Set where
data MineralNIncreaseMeansPlantBenefit : Set where
data MicrobialResponseMeansDecompositionRate : Set where
data P5991MeansP14143 : Set where
data P854MeansVerifiedAuthority : Set where
data QidMeansPrimarySource : Set where
data SamePaperMeansSameSystemBoundary : Set where
data AcquisitionMeansPayment : Set where

localSoilFluxDoesNotBecomeAnnualEntityGHG : LocalSoilCO2FluxMeansAnnualEntityGHG → ⊥
localSoilFluxDoesNotBecomeAnnualEntityGHG ()

soilCarbonStockDoesNotBecomeCarbonFootprint : SoilCarbonStockMeansCarbonFootprint → ⊥
soilCarbonStockDoesNotBecomeCarbonFootprint ()

soilWarmingResponseDoesNotBecomeClimateAttribution : SoilWarmingResponseMeansClimateAttribution → ⊥
soilWarmingResponseDoesNotBecomeClimateAttribution ()

mineralNIncreaseDoesNotGuaranteePlantBenefit : MineralNIncreaseMeansPlantBenefit → ⊥
mineralNIncreaseDoesNotGuaranteePlantBenefit ()

microbialResponseDoesNotIdentifyDecompositionRate : MicrobialResponseMeansDecompositionRate → ⊥
microbialResponseDoesNotIdentifyDecompositionRate ()

p5991DoesNotDefinitionallyEqualP14143 : P5991MeansP14143 → ⊥
p5991DoesNotDefinitionallyEqualP14143 ()

p854DoesNotCreateVerifiedAuthority : P854MeansVerifiedAuthority → ⊥
p854DoesNotCreateVerifiedAuthority ()

qidDoesNotCreatePrimarySource : QidMeansPrimarySource → ⊥
qidDoesNotCreatePrimarySource ()

samePaperDoesNotCreateSameSystemBoundary : SamePaperMeansSameSystemBoundary → ⊥
samePaperDoesNotCreateSameSystemBoundary ()

acquisitionDoesNotCreatePayment : AcquisitionMeansPayment → ⊥
acquisitionDoesNotCreatePayment ()

record SoilClimateLESBoundary : Set where
  constructor soil-climate-les-boundary
  field
    soilBiologyReused : Bool
    ecologyBiogeochemistryReused : Bool
    NatClimateHandoffReused : Bool
    primaryWarmingSourcesStayExternal : Bool
    QIDsStayIdentityOnly : Bool
    localEcologicalFluxCollapsedIntoCorporateAccounting : Bool
    warmingExperimentAutomaticallyCreatesGlobalClimateAttribution : Bool
    p5991P14143AutomaticallyEquivalent : Bool
    acquisitionAutomaticallyAdvancesPayment : Bool
    currentAxisVocabularyClaimedComplete : Bool

canonicalSoilClimateLESBoundary : SoilClimateLESBoundary
canonicalSoilClimateLESBoundary =
  soil-climate-les-boundary true true true true true false false false false false
