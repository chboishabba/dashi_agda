module DASHI.Wikimedia.IbrahimSnowballBiodiversityNutrientRestorationLESExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballEcologyEcosystemBiogeochemistryLESExact as Prior

------------------------------------------------------------------------
-- IBRAHIM / LES BIOLOGY-ECOLOGY SECOND-ORDER CONTINUATION
--
-- ecology / ecosystem / soil ecology / biogeochemistry
--      <-> biodiversity / plant ecology
--      <-> nutrient cycling
--      <-> restoration ecology / succession
--
-- External QIDs are identity/navigation coordinates only.  Primary field
-- experiments are separate source objects.  Neither QID adjacency nor source
-- citation creates a universal ecological effect, restoration success, local
-- nutrient closure, transport, or management recommendation.
------------------------------------------------------------------------

biodiversityQid : Identity.ExternalIdentityDemand
biodiversityQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES biodiversity continuation" "external ecological concept identity"
  "biodiversity" Identity.wikidataQid
  (Identity.verified "Q47041" "Wikidata biodiversity identity checked 2026-09-10")

nutrientCycleQid : Identity.ExternalIdentityDemand
nutrientCycleQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES biodiversity continuation" "external process identity"
  "nutrient cycle" Identity.wikidataQid
  (Identity.verified "Q7070482" "Wikidata nutrient-cycle identity checked 2026-09-10")

soilQid : Identity.ExternalIdentityDemand
soilQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES biodiversity continuation" "external material/environment identity"
  "soil" Identity.wikidataQid
  (Identity.verified "Q36133" "Wikidata soil identity checked 2026-09-10; distinguished from the band/item homonym")

plantEcologyQid : Identity.ExternalIdentityDemand
plantEcologyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES biodiversity continuation" "external ecology-subdiscipline identity"
  "plant ecology" Identity.wikidataQid
  (Identity.verified "Q1387972" "Wikidata plant-ecology identity checked 2026-09-10")

restorationEcologyQid : Identity.ExternalIdentityDemand
restorationEcologyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES biodiversity continuation" "external discipline identity"
  "restoration ecology" Identity.wikidataQid
  (Identity.verified "Q2428433" "Wikidata restoration-ecology identity checked 2026-09-10")

------------------------------------------------------------------------
-- Primary empirical source: direct field manipulation of plant diversity.
------------------------------------------------------------------------

data EcologyFieldSourceRole : Set where
  biodiversityProductivityFieldExperiment : EcologyFieldSourceRole

record EcologyFieldPrimarySource : Set where
  constructor ecology-field-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    role : EcologyFieldSourceRole
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open EcologyFieldPrimarySource public

tilmanWedinKnops1996 : EcologyFieldPrimarySource
tilmanWedinKnops1996 = ecology-field-primary-source
  "David Tilman; David Wedin; Johannes Knops"
  "Productivity and sustainability influenced by biodiversity in grassland ecosystems"
  "Nature 379:718-720"
  1996
  "DOI 10.1038/379718a0"
  biodiversityProductivityFieldExperiment
  "Well-replicated grassland field experiment in which plant species diversity was directly manipulated and ecosystem productivity was measured."
  "Does not establish a universal biodiversity-productivity law, identify every mechanism, prove restoration success, close every nutrient budget, or transport automatically to other ecosystems."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

record BiodiversityFieldAdmission : Set where
  constructor biodiversity-field-admission
  field
    source : EcologyFieldPrimarySource
    exactSiteReference : String
    plotIdentityReference : String
    manipulatedDiversityReference : String
    plantCompositionReference : String
    productivityMeasurementReference : String
    nutrientConsumerReference : String
    uncertaintyReference : String
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner
    dashiCrosswalkOwner : Attribution.ClaimOwner
    dashiOwnsCrosswalkOnly : dashiCrosswalkOwner ≡ Attribution.dashiFormalisationOwner

open BiodiversityFieldAdmission public

------------------------------------------------------------------------
-- BIDI graph constraints.
------------------------------------------------------------------------

data BiodiversityLESNode : Set where
  biodiversityNode soilNode plantEcologyNode nutrientCycleNode restorationNode : BiodiversityLESNode

record BiodiversityLESGraphAudit : Set where
  constructor biodiversity-les-graph-audit
  field
    node : BiodiversityLESNode
    upwardReading : String
    downwardConstraint : String
    wrongTypeRisk : String
    qidIsIdentityOnly : Bool
    sourceAttributionRequired : Bool
    localPhysicalReceiptRequired : Bool

open BiodiversityLESGraphAudit public

biodiversityAudit : BiodiversityLESGraphAudit
biodiversityAudit = biodiversity-les-graph-audit biodiversityNode
  "variation-of-life ecological coordinate adjacent to community structure and ecosystem function"
  "species richness, identity, functional composition, abundance and spatial structure remain distinct consumers"
  "biodiversity label != species richness alone != ecosystem function != restoration success"
  true true true

nutrientCycleAudit : BiodiversityLESGraphAudit
nutrientCycleAudit = biodiversity-les-graph-audit nutrientCycleNode
  "process family exchanging nutrients among system compartments"
  "local stocks, transformations, uptake, export, loss and residual require explicit conservation receipts"
  "nutrient-cycle membership != closed local budget != plant availability != uptake"
  true true true

restorationAudit : BiodiversityLESGraphAudit
restorationAudit = biodiversity-les-graph-audit restorationNode
  "restoration-science coordinate linking intervention, reference state and ecological trajectory"
  "biodiversity response and nutrient response must be observed under an exact intervention/reference/horizon carrier"
  "restoration action != historical-state recovery != biodiversity benefit != resilience"
  true true true

------------------------------------------------------------------------
-- Snowball: later evidence may be retained before earlier gates are paid.
------------------------------------------------------------------------

record BiodiversityLESAcquisitionState : Set where
  constructor biodiversity-les-acquisition-state
  field
    biodiversityQidAcquired : Bool
    nutrientCycleQidAcquired : Bool
    soilQidAcquired : Bool
    plantEcologyQidAcquired : Bool
    restorationEcologyQidAcquired : Bool
    primaryBiodiversityExperimentAcquired : Bool
    speciesRichnessEvidenceAcquired : Bool
    compositionEvidenceAcquired : Bool
    productivityEvidenceAcquired : Bool
    soilNitrogenEvidenceAcquired : Bool
    nutrientLossEvidenceAcquired : Bool
    restorationTrajectoryEvidenceAcquired : Bool
    replicationEvidenceAcquired : Bool
    transportEvidenceAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open BiodiversityLESAcquisitionState public

record BiodiversityLESPaymentState : Set where
  constructor biodiversity-les-payment-state
  field
    qidIdentityPaid : Bool
    exactSourceIdentityPaid : Bool
    sourceRoleAttributionPaid : Bool
    sitePlotIdentityPaid : Bool
    interventionIdentityPaid : Bool
    diversityCompositionDisambiguationPaid : Bool
    productivityConsumerPaid : Bool
    nutrientConsumerPaid : Bool
    nutrientMassBalancePaid : Bool
    restorationComparatorPaid : Bool
    causalIdentificationPaid : Bool
    replicationPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open BiodiversityLESPaymentState public

snowballAcquisitionDoesNotAdvanceBiodiversityLESPayment :
  BiodiversityLESAcquisitionState → BiodiversityLESPaymentState → BiodiversityLESPaymentState
snowballAcquisitionDoesNotAdvanceBiodiversityLESPayment _ payment = payment

------------------------------------------------------------------------
-- No-promotion / WrongType firewalls.
------------------------------------------------------------------------

data QidCreatesBiodiversityEvidence : Set where
data SpeciesRichnessEqualsBiodiversity : Set where
data SameRichnessEqualsSameComposition : Set where
data BiodiversityCreatesProductivity : Set where
data ProductivityCreatesNutrientClosure : Set where
data NutrientCycleCreatesPlantAvailability : Set where
data RestorationCreatesBiodiversityBenefit : Set where
data OneGrasslandExperimentCreatesUniversalLaw : Set where
data ExternalSourceOwnsDashiInference : Set where
data AcquisitionCreatesPayment : Set where

qidDoesNotCreateBiodiversityEvidence : QidCreatesBiodiversityEvidence → ⊥
qidDoesNotCreateBiodiversityEvidence ()

speciesRichnessDoesNotExhaustBiodiversity : SpeciesRichnessEqualsBiodiversity → ⊥
speciesRichnessDoesNotExhaustBiodiversity ()

sameRichnessDoesNotCreateSameComposition : SameRichnessEqualsSameComposition → ⊥
sameRichnessDoesNotCreateSameComposition ()

biodiversityLabelDoesNotCreateProductivity : BiodiversityCreatesProductivity → ⊥
biodiversityLabelDoesNotCreateProductivity ()

productivityDoesNotCreateNutrientClosure : ProductivityCreatesNutrientClosure → ⊥
productivityDoesNotCreateNutrientClosure ()

nutrientCycleDoesNotCreatePlantAvailability : NutrientCycleCreatesPlantAvailability → ⊥
nutrientCycleDoesNotCreatePlantAvailability ()

restorationDoesNotCreateBiodiversityBenefit : RestorationCreatesBiodiversityBenefit → ⊥
restorationDoesNotCreateBiodiversityBenefit ()

oneGrasslandExperimentDoesNotCreateUniversalLaw : OneGrasslandExperimentCreatesUniversalLaw → ⊥
oneGrasslandExperimentDoesNotCreateUniversalLaw ()

externalSourceDoesNotOwnDashiInference : ExternalSourceOwnsDashiInference → ⊥
externalSourceDoesNotOwnDashiInference ()

acquisitionDoesNotCreatePayment : AcquisitionCreatesPayment → ⊥
acquisitionDoesNotCreatePayment ()

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

priorEcologyBoundary : Prior.EcologyLESSnowballBoundary
priorEcologyBoundary = Prior.canonicalEcologyLESSnowballBoundary
