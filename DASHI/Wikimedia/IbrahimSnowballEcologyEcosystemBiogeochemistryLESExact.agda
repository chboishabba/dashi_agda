module DASHI.Wikimedia.IbrahimSnowballEcologyEcosystemBiogeochemistryLESExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballAnthropologyAgricultureLESExact as Prior
import DASHI.Environment.SoilPlantAtmosphereContinuumExact as SPAC
import DASHI.Environment.QuantitiesConservation as Conservation

------------------------------------------------------------------------
-- IBRAHIM / LES BIOLOGY-ECOLOGY SNOWBALL CONTINUATION
--
-- agriculture Q11451 -> agroecology Q396338 -> agronomy Q173113
--                    <-> ecology / ecosystem
--                    <-> soil / landscape ecology
--                    <-> water / carbon / biogeochemical cycles
--                    <-> succession / restoration / resilience consumers
--
-- QIDs below are external identity/navigation coordinates.  They do not pay
-- mechanism, conservation, causal effect, restoration success, resilience,
-- transport, or recommendation.  Existing DASHI SPAC/conservation owners remain
-- authoritative for physical payment; external source attribution travels with
-- every source-derived proposition.
------------------------------------------------------------------------

ecologyQid : Identity.ExternalIdentityDemand
ecologyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES ecology continuation" "external discipline identity"
  "ecology" Identity.wikidataQid
  (Identity.verified "Q7150" "Wikidata ecology identity checked 2026-09-10")

ecosystemQid : Identity.ExternalIdentityDemand
ecosystemQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES ecology continuation" "external system-concept identity"
  "ecosystem" Identity.wikidataQid
  (Identity.verified "Q37813" "Wikidata ecosystem identity checked 2026-09-10")

soilEcologyQid : Identity.ExternalIdentityDemand
soilEcologyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES ecology continuation" "external ecology subdiscipline identity"
  "soil ecology" Identity.wikidataQid
  (Identity.verified "Q450056" "Wikidata soil-ecology identity checked 2026-09-10")

landscapeEcologyQid : Identity.ExternalIdentityDemand
landscapeEcologyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES ecology continuation" "external ecology subdiscipline identity"
  "landscape ecology" Identity.wikidataQid
  (Identity.verified "Q738011" "Wikidata landscape-ecology identity checked 2026-09-10")

restorationEcologyQid : Identity.ExternalIdentityDemand
restorationEcologyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES ecology continuation" "external ecology subdiscipline identity"
  "restoration ecology" Identity.wikidataQid
  (Identity.verified "Q2428433" "Wikidata restoration-ecology identity checked 2026-09-10")

ecologicalSuccessionQid : Identity.ExternalIdentityDemand
ecologicalSuccessionQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES ecology continuation" "external ecological-process identity"
  "ecological succession" Identity.wikidataQid
  (Identity.verified "Q188230" "Wikidata ecological-succession identity checked 2026-09-10")

biogeochemicalCycleQid : Identity.ExternalIdentityDemand
biogeochemicalCycleQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES ecology continuation" "external process-family identity"
  "biogeochemical cycle" Identity.wikidataQid
  (Identity.verified "Q846303" "Wikidata biogeochemical-cycle identity checked 2026-09-10")

carbonCycleQid : Identity.ExternalIdentityDemand
carbonCycleQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES ecology continuation" "external cycle identity"
  "carbon cycle" Identity.wikidataQid
  (Identity.verified "Q167751" "Wikidata carbon-cycle identity checked 2026-09-10")

waterCycleQid : Identity.ExternalIdentityDemand
waterCycleQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES ecology continuation" "external cycle identity"
  "water cycle" Identity.wikidataQid
  (Identity.verified "Q81041" "Wikidata water-cycle identity checked 2026-09-10")

------------------------------------------------------------------------
-- BIDI graph roles.  A parent label creates a search obligation; it cannot
-- erase the consumer coordinates needed by a concrete ecological experiment.
------------------------------------------------------------------------

data EcologyLESNode : Set where
  ecologyNode ecosystemNode soilEcologyNode landscapeEcologyNode
  restorationEcologyNode successionNode biogeochemicalCycleNode
  carbonCycleNode waterCycleNode : EcologyLESNode

record EcologyLESGraphAudit : Set where
  constructor ecology-les-graph-audit
  field
    node : EcologyLESNode
    upwardNavigationReading : String
    downwardConsumerConstraint : String
    principalWrongTypeRisk : String
    qidIsIdentityOnly : Bool
    attributionRequired : Bool
    physicalReceiptStillRequired : Bool
    parentLabelExplainsEveryChildCase : Bool

open EcologyLESGraphAudit public

ecosystemAudit : EcologyLESGraphAudit
ecosystemAudit = ecology-les-graph-audit ecosystemNode
  "living organisms plus nonliving environment interacting as a system"
  "local LES still requires explicit state, boundary, observation, intervention and conservation coordinates"
  "ecosystem label != identified local ecosystem state != causal mechanism"
  true true true false

soilEcologyAudit : EcologyLESGraphAudit
soilEcologyAudit = ecology-les-graph-audit soilEcologyNode
  "soil-organism and biotic/abiotic interaction discipline"
  "soil hydraulic state, mineral-N state, microbial process and root uptake remain separate physical consumers"
  "soil ecology != soil hydraulic calibration != nutrient closure"
  true true true false

landscapeEcologyAudit : EcologyLESGraphAudit
landscapeEcologyAudit = ecology-les-graph-audit landscapeEcologyNode
  "spatial relations between ecological processes and landscape/ecosystem structure"
  "landscape pattern cannot recover a local process effect without same-site spatial and causal receipts"
  "landscape adjacency != mechanism != local treatment effect"
  true true true false

restorationAudit : EcologyLESGraphAudit
restorationAudit = ecology-les-graph-audit restorationEcologyNode
  "scientific study of renewing/restoring ecosystems"
  "restoration intervention, reference condition, trajectory, time horizon and measured outcomes must remain explicit"
  "restoration activity != restored historical state != ecological benefit"
  true true true false

successionAudit : EcologyLESGraphAudit
successionAudit = ecology-les-graph-audit successionNode
  "change in ecological community structure through time"
  "observed temporal ordering does not establish deterministic recovery, target state or intervention effect"
  "succession != deterministic progress != restoration success"
  true true true false

biogeochemicalAudit : EcologyLESGraphAudit
biogeochemicalAudit = ecology-les-graph-audit biogeochemicalCycleNode
  "movement/transformation of elements or molecules through biotic and abiotic compartments"
  "N/C/P/water stocks, fluxes, exports and residuals remain separately balanced"
  "named cycle != closed local budget != zero loss"
  true true true false

carbonAudit : EcologyLESGraphAudit
carbonAudit = ecology-les-graph-audit carbonCycleNode
  "carbon exchange among biosphere and other Earth compartments"
  "local carbon stock change, respiration, export and system boundary remain explicit"
  "carbon-cycle participation != net sequestration != climate benefit"
  true true true false

waterAudit : EcologyLESGraphAudit
waterAudit = ecology-les-graph-audit waterCycleNode
  "continuous water movement across Earth-system compartments"
  "site water balance still requires rainfall/input, storage, evapotranspiration, runoff/export and residual receipts"
  "water-cycle membership != situated water closure != plant water availability"
  true true true false

------------------------------------------------------------------------
-- Source lineage.  These are exact publication records with bounded roles.
-- Odum and Holling are theoretical/original conceptual sources, not field
-- experiment receipts. Sperry/Stiller/Hacke is the canonical SPAC source already
-- owned by the environmental model; the DASHI crosswalk does not transfer
-- authorship of the source or source claims to DASHI.
------------------------------------------------------------------------

data EcologyLESSourceRole : Set where
  spacMechanismLineage ecosystemDevelopmentTheory resilienceTheory : EcologyLESSourceRole

record EcologyLESPrimarySource : Set where
  constructor ecology-les-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    role : EcologyLESSourceRole
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open EcologyLESPrimarySource public

sperryStillerHacke2003 : EcologyLESPrimarySource
sperryStillerHacke2003 = ecology-les-primary-source
  "John S. Sperry; Volker Stiller; Uwe G. Hacke"
  "Xylem Hydraulics and the Soil-Plant-Atmosphere Continuum: Opportunities and Unresolved Issues"
  "Agronomy Journal 95(6):1362-1370"
  2003
  "DOI 10.2134/agronj2003.1362"
  spacMechanismLineage
  "Primary publication grounding the soil-xylem-plant hydraulic linkage used by the canonical SPAC owner."
  "Does not by itself instantiate a particular LES state, close nutrient/carbon balances, identify causal intervention effects or validate every site."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

odum1969 : EcologyLESPrimarySource
odum1969 = ecology-les-primary-source
  "Eugene P. Odum"
  "The Strategy of Ecosystem Development"
  "Science 164(3877):262-270"
  1969
  "DOI 10.1126/science.164.3877.262; PMID 5776636"
  ecosystemDevelopmentTheory
  "Original theoretical synthesis relating ecosystem development and succession."
  "Theory source does not establish deterministic succession, restoration success, local causal effect or universal ecosystem trajectory."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

holling1973 : EcologyLESPrimarySource
holling1973 = ecology-les-primary-source
  "C. S. Holling"
  "Resilience and Stability of Ecological Systems"
  "Annual Review of Ecology and Systematics 4:1-23"
  1973
  "DOI 10.1146/annurev.es.04.110173.000245"
  resilienceTheory
  "Original resilience/stability theoretical source retained as conceptual lineage."
  "Does not by itself measure resilience of a present LES site, prove recovery from a disturbance, or justify a management recommendation."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

record EcologyLESSourceAdmission : Set where
  constructor ecology-les-source-admission
  field
    source : EcologyLESPrimarySource
    exactConsumerReference : String
    exactSourceRoleReference : String
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner
    dashiCrosswalkOwner : Attribution.ClaimOwner
    dashiOwnsCrosswalkOnly : dashiCrosswalkOwner ≡ Attribution.dashiFormalisationOwner

open EcologyLESSourceAdmission public

------------------------------------------------------------------------
-- Existing physical owners pay the mechanism/conservation layer.
------------------------------------------------------------------------

record EcologyLESSPACAdmission (spac : SPAC.SPACDomainRealization) : Set₁ where
  constructor ecology-les-spac-admission
  field
    exactLESStateReference : String
    exactSiteHistoryReference : String
    exactSpatialBoundaryReference : String
    exactTemporalBoundaryReference : String
    soilHydraulicConsumerReference : String
    rootUptakeConsumerReference : String
    soilBiogeochemistryConsumerReference : String
    plantCarbonAllocationConsumerReference : String
    transpirationWaterBalanceConsumerReference : String
    crossDomainConservationReference : String
    heldOutValidationReference : String
    dashiFormalisationOwner : Attribution.ClaimOwner
    dashiOwnsPhysicalAdmission : dashiFormalisationOwner ≡ Attribution.dashiFormalisationOwner

open EcologyLESSPACAdmission public

spacBoundary : SPAC.SPACBoundary
spacBoundary = SPAC.canonicalSPACBoundary

------------------------------------------------------------------------
-- Snowball execution: collect broadly, pay narrowly.
------------------------------------------------------------------------

record EcologyLESAcquisitionState : Set where
  constructor ecology-les-acquisition-state
  field
    ecologyQidAcquired : Bool
    ecosystemQidAcquired : Bool
    soilEcologyQidAcquired : Bool
    landscapeEcologyQidAcquired : Bool
    restorationEcologyQidAcquired : Bool
    successionQidAcquired : Bool
    biogeochemicalCycleQidAcquired : Bool
    carbonCycleQidAcquired : Bool
    waterCycleQidAcquired : Bool
    spacPrimarySourceAcquired : Bool
    ecosystemTheorySourceAcquired : Bool
    resilienceTheorySourceAcquired : Bool
    soilWaterEvidenceAcquired : Bool
    nutrientEvidenceAcquired : Bool
    carbonEvidenceAcquired : Bool
    biodiversityEvidenceAcquired : Bool
    restorationTrajectoryEvidenceAcquired : Bool
    disturbanceRecoveryEvidenceAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open EcologyLESAcquisitionState public

record EcologyLESPaymentState : Set where
  constructor ecology-les-payment-state
  field
    qidIdentityPaid : Bool
    conceptSensePaid : Bool
    exactSourceIdentityPaid : Bool
    sourceRoleAttributionPaid : Bool
    exactSiteHistoryPaid : Bool
    exactSystemBoundaryPaid : Bool
    spacMechanismPaid : Bool
    waterBalancePaid : Bool
    nitrogenBalancePaid : Bool
    carbonBalancePaid : Bool
    biodiversityConsumerPaid : Bool
    disturbanceIdentityPaid : Bool
    restorationComparatorPaid : Bool
    resilienceOperationalisationPaid : Bool
    causalIdentificationPaid : Bool
    heldOutValidationPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open EcologyLESPaymentState public

snowballAcquisitionDoesNotAdvanceEcologyLESPayment :
  EcologyLESAcquisitionState → EcologyLESPaymentState → EcologyLESPaymentState
snowballAcquisitionDoesNotAdvanceEcologyLESPayment _ payment = payment

------------------------------------------------------------------------
-- WrongType / no-promotion firewalls.
------------------------------------------------------------------------

data QidCreatesEcologicalEvidence : Set where
data EcologyLabelCreatesMechanism : Set where
data EcosystemLabelCreatesSameObject : Set where
data NamedCycleCreatesClosedBudget : Set where
data WaterCycleCreatesSiteWaterBalance : Set where
data CarbonCycleCreatesSequestration : Set where
data SuccessionCreatesRestorationSuccess : Set where
data RestorationActivityCreatesReferenceState : Set where
data ResilienceTheoryCreatesMeasuredResilience : Set where
data AdjacentQidCreatesTechnicalDependency : Set where
data ExternalSourceOwnsDashiCrosswalk : Set where
data AcquisitionCreatesPayment : Set where

qidDoesNotCreateEcologicalEvidence : QidCreatesEcologicalEvidence → ⊥
qidDoesNotCreateEcologicalEvidence ()

ecologyLabelDoesNotCreateMechanism : EcologyLabelCreatesMechanism → ⊥
ecologyLabelDoesNotCreateMechanism ()

ecosystemLabelDoesNotCreateSameObject : EcosystemLabelCreatesSameObject → ⊥
ecosystemLabelDoesNotCreateSameObject ()

namedCycleDoesNotCreateClosedBudget : NamedCycleCreatesClosedBudget → ⊥
namedCycleDoesNotCreateClosedBudget ()

waterCycleDoesNotPaySiteWaterBalance : WaterCycleCreatesSiteWaterBalance → ⊥
waterCycleDoesNotPaySiteWaterBalance ()

carbonCycleDoesNotPaySequestration : CarbonCycleCreatesSequestration → ⊥
carbonCycleDoesNotPaySequestration ()

successionDoesNotPayRestorationSuccess : SuccessionCreatesRestorationSuccess → ⊥
successionDoesNotPayRestorationSuccess ()

restorationActivityDoesNotCreateReferenceState : RestorationActivityCreatesReferenceState → ⊥
restorationActivityDoesNotCreateReferenceState ()

resilienceTheoryDoesNotPayMeasuredResilience : ResilienceTheoryCreatesMeasuredResilience → ⊥
resilienceTheoryDoesNotPayMeasuredResilience ()

qidAdjacencyDoesNotCreateTechnicalDependency : AdjacentQidCreatesTechnicalDependency → ⊥
qidAdjacencyDoesNotCreateTechnicalDependency ()

externalSourceDoesNotOwnDashiCrosswalk : ExternalSourceOwnsDashiCrosswalk → ⊥
externalSourceDoesNotOwnDashiCrosswalk ()

acquisitionDoesNotCreatePayment : AcquisitionCreatesPayment → ⊥
acquisitionDoesNotCreatePayment ()

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

priorLESBoundary : Prior.AnthropologyAgricultureLESSnowballBoundary
priorLESBoundary = Prior.canonicalAnthropologyAgricultureLESSnowballBoundary

record EcologyEcosystemBiogeochemistryLESBoundary : Set where
  constructor ecology-ecosystem-biogeochemistry-les-boundary
  field
    externalQidsRetainedAsNavigationOnly : Bool
    primarySourceRolesRetained : Bool
    SPACAndConservationRemainPhysicalOwners : Bool
    cyclesAndLocalBalancesRemainDistinct : Bool
    successionAndRestorationRemainDistinct : Bool
    resilienceTheoryAndMeasuredRecoveryRemainDistinct : Bool
    acquisitionAndPaymentRemainDistinct : Bool
    currentAxisVocabularyClaimedComplete : Bool

canonicalEcologyEcosystemBiogeochemistryLESBoundary :
  EcologyEcosystemBiogeochemistryLESBoundary
canonicalEcologyEcosystemBiogeochemistryLESBoundary =
  ecology-ecosystem-biogeochemistry-les-boundary
    true true true true true true true false
