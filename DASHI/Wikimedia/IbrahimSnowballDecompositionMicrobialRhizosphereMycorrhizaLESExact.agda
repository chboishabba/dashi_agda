module DASHI.Wikimedia.IbrahimSnowballDecompositionMicrobialRhizosphereMycorrhizaLESExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballBiodiversityNutrientRestorationLESExact as Prior
import DASHI.Environment.KoreanNaturalFarmingExact as KNF
import DASHI.Environment.SoilPlantAtmosphereContinuumExact as SPAC

------------------------------------------------------------------------
-- IBRAHIM / LES BIOLOGY-ECOLOGY CONTINUATION
--
-- biodiversity / nutrient cycle / restoration
--   <-> decomposition / microbial ecology
--   <-> rhizosphere / mycorrhiza / arbuscular mycorrhiza
--   <-> root carbon allocation / soil respiration / nutrient capture
--   <-> KNF microbial-practice and SPAC physical consumers
--
-- QIDs are identity/navigation coordinates only. Primary publications retain
-- external authorship. DASHI owns only the formal crosswalk/inference layer.
-- Acquisition may snowball out of order; payment remains exact and consumer-
-- relative. The broad `soil food web` QID remains unresolved here rather than
-- promoting a paper/thesis/category item into the concept identity.
------------------------------------------------------------------------

decompositionQid : Identity.ExternalIdentityDemand
decompositionQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES decomposition/rhizosphere continuation" "external ecological-process identity"
  "decomposition" Identity.wikidataQid
  (Identity.verified "Q339062" "Wikidata decomposition identity checked 2026-09-10")

microbialEcologyQid : Identity.ExternalIdentityDemand
microbialEcologyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES decomposition/rhizosphere continuation" "external ecology-discipline identity"
  "microbial ecology" Identity.wikidataQid
  (Identity.verified "Q3054637" "Wikidata microbial-ecology identity checked 2026-09-10")

rhizosphereQid : Identity.ExternalIdentityDemand
rhizosphereQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES decomposition/rhizosphere continuation" "external root-zone ecosystem identity"
  "rhizosphere" Identity.wikidataQid
  (Identity.verified "Q1124578" "Wikidata rhizosphere identity checked 2026-09-10")

mycorrhizaQid : Identity.ExternalIdentityDemand
mycorrhizaQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES decomposition/rhizosphere continuation" "external symbiosis identity"
  "mycorrhiza" Identity.wikidataQid
  (Identity.verified "Q99974" "Wikidata mycorrhiza identity checked 2026-09-10")

arbuscularMycorrhizaQid : Identity.ExternalIdentityDemand
arbuscularMycorrhizaQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES decomposition/rhizosphere continuation" "external mycorrhiza subtype identity"
  "arbuscular mycorrhiza" Identity.wikidataQid
  (Identity.verified "Q520825" "Wikidata arbuscular-mycorrhiza identity checked 2026-09-10")

soilFoodWebQid : Identity.ExternalIdentityDemand
soilFoodWebQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES decomposition/rhizosphere continuation" "external ecological-network identity"
  "soil food web" Identity.wikidataQid
  (Identity.unresolved "exact broad soil-food-web concept QID not safely resolved; article/thesis items are not promoted")

------------------------------------------------------------------------
-- Primary source carriers. These are experiments, not QID authorities.
------------------------------------------------------------------------

data SoilBiologySourceRole : Set where
  rootCarbonSoilRespirationExperiment
  mycorrhizalDiversityEcosystemExperiment : SoilBiologySourceRole

record SoilBiologyPrimarySource : Set where
  constructor soil-biology-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    role : SoilBiologySourceRole
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open SoilBiologyPrimarySource public

hogbergEtAl2001 : SoilBiologyPrimarySource
hogbergEtAl2001 = soil-biology-primary-source
  "Peter Högberg; Anders Nordgren; Nina Buchmann; Andrew F. S. Taylor; Alf Ekblad; Mona N. Högberg; Gert Nyberg; Mikaell Ottosson-Löfvenius; David J. Read"
  "Large-scale forest girdling shows that current photosynthesis drives soil respiration"
  "Nature 411:789-792"
  2001
  "DOI 10.1038/35081058; PMID 11459055"
  rootCarbonSoilRespirationExperiment
  "Large-scale boreal pine girdling experiment interrupted current photosynthate supply to roots/mycorrhizal fungi and measured the resulting soil-respiration response."
  "Does not isolate every decomposer taxon, equate soil respiration with decomposition, establish KNF inoculant efficacy, or transport the measured fraction to arbitrary soils/crops."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

vanDerHeijdenEtAl1998 : SoilBiologyPrimarySource
vanDerHeijdenEtAl1998 = soil-biology-primary-source
  "Marcel G. A. van der Heijden; John N. Klironomos; Margot Ursic; Peter Moutoglis; Ruth Streitwolf-Engel; Thomas Boller; Andres Wiemken; Ian R. Sanders"
  "Mycorrhizal fungal diversity determines plant biodiversity, ecosystem variability and productivity"
  "Nature 396:69-72"
  1998
  "DOI 10.1038/23932"
  mycorrhizalDiversityEcosystemExperiment
  "Two complementary experiments manipulated arbuscular-mycorrhizal fungal composition/richness and measured plant biodiversity, nutrient capture, productivity and variability under bounded experimental systems."
  "Does not prove that any mycorrhizal inoculum is beneficial, that genus-level identity predicts function, that field colonisation occurs after application, or that the experimental effect transports universally."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

record SoilBiologySourceAdmission : Set where
  constructor soil-biology-source-admission
  field
    source : SoilBiologyPrimarySource
    exactExperimentalCarrierReference : String
    exactConsumerReference : String
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner
    dashiCrosswalkOwner : Attribution.ClaimOwner
    dashiOwnsCrosswalkOnly : dashiCrosswalkOwner ≡ Attribution.dashiFormalisationOwner

open SoilBiologySourceAdmission public

------------------------------------------------------------------------
-- LES/KNF/SPAC cross-pollination without ontology collapse.
------------------------------------------------------------------------

record RhizosphereLESSameObjectAdmission (spac : SPAC.SPACDomainRealization) : Set₁ where
  constructor rhizosphere-les-same-object-admission
  field
    exactSiteHistoryReference : String
    exactRootZoneReference : String
    exactPlantIdentityReference : String
    exactSoilIdentityReference : String
    exactTemporalBoundaryReference : String
    microbialCommunityMeasurementReference : String
    rootCarbonAllocationReference : String
    mineralNReference : String
    rootUptakeReference : String
    soilRespirationReference : String
    mycorrhizalColonisationReference : String
    nutrientCaptureReference : String
    crossDomainConservationReference : String
    heldOutValidationReference : String

open RhizosphereLESSameObjectAdmission public

record KNFMicrobialEcologyCrosswalk : Set where
  constructor knf-microbial-ecology-crosswalk
  field
    exactKNFPreparationReference : String
    exactApplicationReference : String
    exactInoculumIdentityReference : String
    exactSiteHistoryReference : String
    microbialCommunityBeforeReference : String
    microbialCommunityAfterReference : String
    colonisationMeasurementReference : String
    nutrientAvailabilityMeasurementReference : String
    plantOutcomeReference : String
    sourceRoleReference : String
    dashiInferenceOwner : Attribution.ClaimOwner
    dashiOwnsCrossSourceInference : dashiInferenceOwner ≡ Attribution.dashiInferenceOwner

open KNFMicrobialEcologyCrosswalk public

knfBoundary : KNF.KoreanNaturalFarmingBoundary
knfBoundary = KNF.canonicalKoreanNaturalFarmingBoundary

spacBoundary : SPAC.SPACBoundary
spacBoundary = SPAC.canonicalSPACBoundary

------------------------------------------------------------------------
-- Snowball acquisition/payment split.
------------------------------------------------------------------------

record SoilBiologyLESAcquisitionState : Set where
  constructor soil-biology-les-acquisition-state
  field
    decompositionQidAcquired : Bool
    microbialEcologyQidAcquired : Bool
    rhizosphereQidAcquired : Bool
    mycorrhizaQidAcquired : Bool
    arbuscularMycorrhizaQidAcquired : Bool
    soilFoodWebQidAcquired : Bool
    hogbergPrimaryExperimentAcquired : Bool
    mycorrhizaDiversityExperimentAcquired : Bool
    rootCarbonEvidenceAcquired : Bool
    soilRespirationEvidenceAcquired : Bool
    microbialCommunityEvidenceAcquired : Bool
    colonisationEvidenceAcquired : Bool
    nutrientCaptureEvidenceAcquired : Bool
    KNFApplicationEvidenceAcquired : Bool
    restorationEvidenceAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open SoilBiologyLESAcquisitionState public

record SoilBiologyLESPaymentState : Set where
  constructor soil-biology-les-payment-state
  field
    qidIdentityPaid : Bool
    conceptSensePaid : Bool
    exactPrimarySourcePaid : Bool
    sourceRoleAttributionPaid : Bool
    exactSiteRootSoilIdentityPaid : Bool
    decompositionConsumerPaid : Bool
    soilRespirationConsumerPaid : Bool
    microbialCommunityConsumerPaid : Bool
    mycorrhizalIdentityPaid : Bool
    colonisationPaid : Bool
    rootCarbonAllocationPaid : Bool
    nutrientCapturePaid : Bool
    KNFInoculumSameObjectPaid : Bool
    causalIdentificationPaid : Bool
    heldOutValidationPaid : Bool
    transportPaid : Bool
    restorationConsumerPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open SoilBiologyLESPaymentState public

snowballAcquisitionDoesNotAdvanceSoilBiologyLESPayment :
  SoilBiologyLESAcquisitionState → SoilBiologyLESPaymentState → SoilBiologyLESPaymentState
snowballAcquisitionDoesNotAdvanceSoilBiologyLESPayment _ payment = payment

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data QidMeansMechanism : Set where
data SoilRespirationMeansDecomposition : Set where
data MicrobialCommunityShiftMeansBenefit : Set where
data MycorrhizaIdentityMeansColonisation : Set where
data ColonisationMeansNutrientBenefit : Set where
data AMFDiversityExperimentMeansKNFIMOEffect : Set where
data LocalInoculumMeansMycorrhizalInoculum : Set where
data SoilFoodWebLabelMeansExactNetwork : Set where
data ExternalSourceOwnsDashiCrosswalk : Set where
data AcquisitionMeansPayment : Set where

qidDoesNotCreateMechanism : QidMeansMechanism → ⊥
qidDoesNotCreateMechanism ()

soilRespirationDoesNotEqualDecomposition : SoilRespirationMeansDecomposition → ⊥
soilRespirationDoesNotEqualDecomposition ()

microbialCommunityShiftDoesNotCreateBenefit : MicrobialCommunityShiftMeansBenefit → ⊥
microbialCommunityShiftDoesNotCreateBenefit ()

mycorrhizaIdentityDoesNotPayColonisation : MycorrhizaIdentityMeansColonisation → ⊥
mycorrhizaIdentityDoesNotPayColonisation ()

colonisationDoesNotPayNutrientBenefit : ColonisationMeansNutrientBenefit → ⊥
colonisationDoesNotPayNutrientBenefit ()

amfExperimentDoesNotPayKNFIMOEffect : AMFDiversityExperimentMeansKNFIMOEffect → ⊥
amfExperimentDoesNotPayKNFIMOEffect ()

localInoculumDoesNotEqualMycorrhizalInoculum : LocalInoculumMeansMycorrhizalInoculum → ⊥
localInoculumDoesNotEqualMycorrhizalInoculum ()

soilFoodWebLabelDoesNotCreateExactNetwork : SoilFoodWebLabelMeansExactNetwork → ⊥
soilFoodWebLabelDoesNotCreateExactNetwork ()

externalSourceDoesNotOwnDashiCrosswalk : ExternalSourceOwnsDashiCrosswalk → ⊥
externalSourceDoesNotOwnDashiCrosswalk ()

acquisitionDoesNotCreatePayment : AcquisitionMeansPayment → ⊥
acquisitionDoesNotCreatePayment ()

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

priorBoundary : Prior.BiodiversityNutrientRestorationLESBoundary
priorBoundary = Prior.canonicalBiodiversityNutrientRestorationLESBoundary
