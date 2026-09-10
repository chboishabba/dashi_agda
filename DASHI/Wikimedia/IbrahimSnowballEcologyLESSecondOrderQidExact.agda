module DASHI.Wikimedia.IbrahimSnowballEcologyLESSecondOrderQidExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballEcologyEcosystemBiogeochemistryLESExact as Prior
import DASHI.Environment.SoilPlantAtmosphereContinuumExact as SPAC

------------------------------------------------------------------------
-- SECOND-ORDER BIOLOGY/ECOLOGY WALK FROM THE LES ECOLOGY OWNER.
--
-- This follows only QIDs that remain close to the active biological/ecological
-- consumers.  The graph is navigation; physical/mechanistic payment remains in
-- the exact domain owners.  Missing cross-branch owners remain unpaid rather
-- than being recreated here.
------------------------------------------------------------------------

plantEcologyQid : Identity.ExternalIdentityDemand
plantEcologyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim ecology LES second order" "external ecology subdiscipline identity"
  "plant ecology" Identity.wikidataQid
  (Identity.verified "Q1387972" "Wikidata ecology-project identity checked 2026-09-10")

microbialEcologyQid : Identity.ExternalIdentityDemand
microbialEcologyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim ecology LES second order" "external ecology subdiscipline identity"
  "microbial ecology" Identity.wikidataQid
  (Identity.verified "Q3054637" "Wikidata ecology-project identity checked 2026-09-10")

aquaticEcologyQid : Identity.ExternalIdentityDemand
aquaticEcologyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim ecology LES second order" "external ecology subdiscipline identity"
  "aquatic ecology" Identity.wikidataQid
  (Identity.verified "Q104196941" "Wikidata ecology-project identity checked 2026-09-10")

freshwaterEcologyQid : Identity.ExternalIdentityDemand
freshwaterEcologyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim ecology LES second order" "external ecology subdiscipline identity"
  "freshwater ecology" Identity.wikidataQid
  (Identity.verified "Q60566657" "Wikidata ecology-project identity checked 2026-09-10")

ecohydrologyQid : Identity.ExternalIdentityDemand
ecohydrologyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim ecology LES second order" "external interdisciplinary-field identity"
  "ecohydrology" Identity.wikidataQid
  (Identity.verified "Q2363192" "Wikidata ecology-project identity checked 2026-09-10")

habitatQid : Identity.ExternalIdentityDemand
habitatQid = Identity.mkOptionalIdentityDemand
  "Ibrahim ecology LES second order" "external ecological-area identity"
  "habitat" Identity.wikidataQid
  (Identity.verified "Q52105" "Wikidata ecology-project identity checked 2026-09-10")

ecologicalNicheQid : Identity.ExternalIdentityDemand
ecologicalNicheQid = Identity.mkOptionalIdentityDemand
  "Ibrahim ecology LES second order" "external ecological-concept identity"
  "ecological niche" Identity.wikidataQid
  (Identity.verified "Q172861" "Wikidata ecology-project identity checked 2026-09-10")

grasslandEcologyQid : Identity.ExternalIdentityDemand
grasslandEcologyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim ecology LES second order" "external ecology subdiscipline identity"
  "grassland ecology" Identity.wikidataQid
  (Identity.verified "Q104800105" "Wikidata ecology-project identity checked 2026-09-10")

forestEcologyQid : Identity.ExternalIdentityDemand
forestEcologyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim ecology LES second order" "external ecology subdiscipline identity"
  "forest ecology" Identity.wikidataQid
  (Identity.verified "Q2249329" "Wikidata ecology-project identity checked 2026-09-10")

------------------------------------------------------------------------
-- Consumer-relative BIDI distinctions.
------------------------------------------------------------------------

data EcologySecondOrderNode : Set where
  plantEcologyNode microbialEcologyNode aquaticEcologyNode freshwaterEcologyNode
  ecohydrologyNode habitatNode nicheNode grasslandEcologyNode forestEcologyNode :
  EcologySecondOrderNode

record EcologySecondOrderAudit : Set where
  constructor ecology-second-order-audit
  field
    node : EcologySecondOrderNode
    graphReading : String
    LESConsumerConstraint : String
    wrongTypeRisk : String
    exactPhysicalOwnerAvailableHere : Bool
    qidCanPayMechanism : Bool

open EcologySecondOrderAudit public

plantEcologyAudit : EcologySecondOrderAudit
plantEcologyAudit = ecology-second-order-audit plantEcologyNode
  "plant abundance/distribution and environmental relationships"
  "plant hydraulic, root uptake, carbon allocation and physiological state remain exact SPAC consumers"
  "plant ecology != plant physiology != SPAC state"
  true false

microbialEcologyAudit : EcologySecondOrderAudit
microbialEcologyAudit = ecology-second-order-audit microbialEcologyNode
  "ecology of microorganisms"
  "soil microbial process, mineralisation, respiration and plant-root coupling remain separately identified"
  "microbial ecology != microbial activity != nutrient mineralisation rate"
  true false

aquaticEcologyAudit : EcologySecondOrderAudit
aquaticEcologyAudit = ecology-second-order-audit aquaticEcologyNode
  "ecology of aquatic environments"
  "water chemistry, hydraulics, aeration, nutrient transformations and organism responses need exact aquatic receipts"
  "aquatic ecology != water-treatment engineering != good water quality"
  false false

freshwaterEcologyAudit : EcologySecondOrderAudit
freshwaterEcologyAudit = ecology-second-order-audit freshwaterEcologyNode
  "freshwater ecosystem study"
  "pond/stream/lake identity, flow, chemistry, habitat and biological response remain separate consumers"
  "freshwater label != same habitat != same treatment response"
  false false

ecohydrologyAudit : EcologySecondOrderAudit
ecohydrologyAudit = ecology-second-order-audit ecohydrologyNode
  "interactions between water and ecosystems"
  "hydrologic boundary, storage/flux and ecological response require a same-site weld"
  "ecohydrology != hydrology alone != ecosystem effect"
  true false

habitatAudit : EcologySecondOrderAudit
habitatAudit = ecology-second-order-audit habitatNode
  "environmental area inhabited by a species/population"
  "presence, use, suitability, resource availability and demographic response remain distinct"
  "habitat != ecological niche != demonstrated habitat quality"
  false false

nicheAudit : EcologySecondOrderAudit
nicheAudit = ecology-second-order-audit nicheNode
  "fit/role of a species under specific environmental conditions"
  "observed occurrence cannot recover all limiting resources, interactions or performance dimensions"
  "niche != habitat != observed presence"
  false false

grasslandEcologyAudit : EcologySecondOrderAudit
grasslandEcologyAudit = ecology-second-order-audit grasslandEcologyNode
  "ecology of grassland systems"
  "fire, grazing, fuel, plant community, soil and herbivore responses remain distinct experiment coordinates"
  "grassland ecology != grazing treatment != pyric-herbivory effect"
  false false

forestEcologyAudit : EcologySecondOrderAudit
forestEcologyAudit = ecology-second-order-audit forestEcologyNode
  "ecology of forest ecosystems"
  "tree structure, succession, carbon, hydrology, disturbance and management remain separately measured"
  "forest ecology != agroforestry != silvicultural treatment effect"
  false false

------------------------------------------------------------------------
-- SPAC is the currently available exact biological/physical bridge on this
-- branch.  Other QID lanes can accumulate evidence without pretending their
-- later domain owners have already been welded here.
------------------------------------------------------------------------

record PlantSoilEcologySPACCrosswalk (spac : SPAC.SPACDomainRealization) : Set₁ where
  constructor plant-soil-ecology-spac-crosswalk
  field
    plantEcologyToPlantStateReference : String
    microbialEcologyToSoilBiogeochemistryReference : String
    ecohydrologyToSoilWaterReference : String
    rootUptakeReference : String
    plantCarbonAllocationReference : String
    microbialRespirationReference : String
    transpirationWaterBalanceReference : String
    sameSpatialBoundaryReference : String
    sameTemporalBoundaryReference : String
    validationReference : String

open PlantSoilEcologySPACCrosswalk public

record EcologySecondOrderAcquisitionState : Set where
  constructor ecology-second-order-acquisition-state
  field
    plantEcologyQidAcquired : Bool
    microbialEcologyQidAcquired : Bool
    aquaticEcologyQidAcquired : Bool
    freshwaterEcologyQidAcquired : Bool
    ecohydrologyQidAcquired : Bool
    habitatQidAcquired : Bool
    nicheQidAcquired : Bool
    grasslandEcologyQidAcquired : Bool
    forestEcologyQidAcquired : Bool
    plantStateEvidenceAcquired : Bool
    soilMicrobialEvidenceAcquired : Bool
    aquaticEvidenceAcquired : Bool
    fireGrazingEvidenceAcquired : Bool
    forestAgroforestryEvidenceAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open EcologySecondOrderAcquisitionState public

record EcologySecondOrderPaymentState : Set where
  constructor ecology-second-order-payment-state
  field
    qidIdentityPaid : Bool
    exactConsumerPaid : Bool
    sameSiteHistoryPaid : Bool
    plantSPACCrosswalkPaid : Bool
    microbialProcessCrosswalkPaid : Bool
    ecohydrologyCrosswalkPaid : Bool
    aquaticDomainWeldPaid : Bool
    habitatPerformancePaid : Bool
    nicheOperationalisationPaid : Bool
    grasslandFireGrazingWeldPaid : Bool
    forestManagementWeldPaid : Bool
    causalIdentificationPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open EcologySecondOrderPaymentState public

snowballAcquisitionDoesNotAdvanceEcologySecondOrderPayment :
  EcologySecondOrderAcquisitionState →
  EcologySecondOrderPaymentState →
  EcologySecondOrderPaymentState
snowballAcquisitionDoesNotAdvanceEcologySecondOrderPayment _ payment = payment

------------------------------------------------------------------------
-- WrongTypes exposed by this QID layer.
------------------------------------------------------------------------

data PlantEcologyMeansPlantPhysiology : Set where
data MicrobialEcologyMeansMineralisation : Set where
data AquaticEcologyMeansWaterTreatment : Set where
data FreshwaterEcologyMeansSameHabitat : Set where
data EcohydrologyMeansWaterBalanceClosure : Set where
data HabitatMeansNiche : Set where
data PresenceMeansHabitatQuality : Set where
data GrasslandEcologyMeansGrazingEffect : Set where
data ForestEcologyMeansAgroforestryEffect : Set where
data MissingDomainOwnerCanBeInventedLocally : Set where

plantEcologyDoesNotEqualPlantPhysiology : PlantEcologyMeansPlantPhysiology → ⊥
plantEcologyDoesNotEqualPlantPhysiology ()

microbialEcologyDoesNotPayMineralisation : MicrobialEcologyMeansMineralisation → ⊥
microbialEcologyDoesNotPayMineralisation ()

aquaticEcologyDoesNotPayWaterTreatment : AquaticEcologyMeansWaterTreatment → ⊥
aquaticEcologyDoesNotPayWaterTreatment ()

freshwaterEcologyDoesNotCreateSameHabitat : FreshwaterEcologyMeansSameHabitat → ⊥
freshwaterEcologyDoesNotCreateSameHabitat ()

ecohydrologyDoesNotPayWaterBalanceClosure : EcohydrologyMeansWaterBalanceClosure → ⊥
ecohydrologyDoesNotPayWaterBalanceClosure ()

habitatDoesNotEqualNiche : HabitatMeansNiche → ⊥
habitatDoesNotEqualNiche ()

presenceDoesNotPayHabitatQuality : PresenceMeansHabitatQuality → ⊥
presenceDoesNotPayHabitatQuality ()

grasslandEcologyDoesNotPayGrazingEffect : GrasslandEcologyMeansGrazingEffect → ⊥
grasslandEcologyDoesNotPayGrazingEffect ()

forestEcologyDoesNotPayAgroforestryEffect : ForestEcologyMeansAgroforestryEffect → ⊥
forestEcologyDoesNotPayAgroforestryEffect ()

missingOwnerIsNotRecreatedHere : MissingDomainOwnerCanBeInventedLocally → ⊥
missingOwnerIsNotRecreatedHere ()

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

priorEcologyBoundary : Prior.EcologyEcosystemBiogeochemistryLESBoundary
priorEcologyBoundary = Prior.canonicalEcologyEcosystemBiogeochemistryLESBoundary

record EcologyLESSecondOrderBoundary : Set where
  constructor ecology-les-second-order-boundary
  field
    secondOrderQidsRetained : Bool
    plantMicrobeWaterConsumersMapToExistingSPAC : Bool
    habitatAndNicheRemainDistinct : Bool
    aquaticQidsDoNotInventMissingPhysicalOwner : Bool
    grasslandAndForestEcologyDoNotPayManagementEffects : Bool
    acquisitionAndPaymentRemainDistinct : Bool
    qidAdjacencyCreatesMechanism : Bool

canonicalEcologyLESSecondOrderBoundary : EcologyLESSecondOrderBoundary
canonicalEcologyLESSecondOrderBoundary =
  ecology-les-second-order-boundary true true true true true true false
