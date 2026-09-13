module DASHI.Wikimedia.IbrahimSnowballTiwiEcosystemTypologyKnowledgeAuthorityDeweyDoiQidExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimCountryCommunityKnowledgeAuthorityBridgeExact as CountryAuthority
import DASHI.Wikimedia.IbrahimSnowballTiwiMultiDriverManagementDeweyDoiQidExact as MultiDriver

------------------------------------------------------------------------
-- TIWI ECOSYSTEM TYPOLOGY / KNOWLEDGE-AUTHORITY FOLLOW
--
-- This owner extends the Tiwi LES/Ibrahim walk from disturbance mechanisms to
-- the ecosystem-classification surface itself.  Local Tiwi ecosystem names,
-- generic Wikidata concepts, Dewey classes, scientific map classes, and Country
-- / knowledge authority are distinct coordinates.  None silently substitutes
-- for another.
------------------------------------------------------------------------

ecosystemQid : Identity.ExternalIdentityDemand
ecosystemQid = Identity.mkOptionalIdentityDemand
  "Tiwi ecosystem typology snowball" "generic ecosystem concept identity"
  "ecosystem" Identity.wikidataQid
  (Identity.verified "Q37813" "Wikidata ecosystem item inspected 2026-09-11; concept identity only")

savannaQid : Identity.ExternalIdentityDemand
savannaQid = Identity.mkOptionalIdentityDemand
  "Tiwi ecosystem typology snowball" "generic savanna concept identity"
  "savanna" Identity.wikidataQid
  (Identity.verified "Q42320" "Wikidata savanna item inspected 2026-09-11; generic biome/ecosystem identity does not identify a Tiwi ecosystem type")

wetlandQid : Identity.ExternalIdentityDemand
wetlandQid = Identity.mkOptionalIdentityDemand
  "Tiwi ecosystem typology snowball" "generic wetland concept identity"
  "wetland" Identity.wikidataQid
  (Identity.verified "Q170321" "Wikidata wetland item inspected 2026-09-11")

mangroveEcosystemQid : Identity.ExternalIdentityDemand
mangroveEcosystemQid = Identity.mkOptionalIdentityDemand
  "Tiwi ecosystem typology snowball" "mangrove vegetation / biome identity"
  "mangrove ecosystem / vegetation" Identity.wikidataQid
  (Identity.verified "Q19756" "Wikidata mangrove vegetation/biome item inspected 2026-09-11; kept distinct from mangrove organism item Q1372331")

plantationQid : Identity.ExternalIdentityDemand
plantationQid = Identity.mkOptionalIdentityDemand
  "Tiwi ecosystem typology snowball" "plantation concept identity"
  "plantation" Identity.wikidataQid
  (Identity.verified "Q188913" "Wikidata plantation item inspected 2026-09-11; not the place-name item Plantation, Florida")

------------------------------------------------------------------------
-- Dewey is consumer-indexed.  The same savanna concept can be classified as
-- ecology or as societal management of grasslands.  This is not inconsistency:
-- it reflects different works / consumers.
------------------------------------------------------------------------

ecosystemEcologyCoordinate : Traversal.DashiKnowledgeCoordinate
ecosystemEcologyCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiEcosystemTypologyKnowledgeAuthorityDeweyDoiQidExact.agda"
  "ecosystem / terrestrial ecology"
  "577 — ecology; OCLC classes biomes, ecosystems and terrestrial ecology here"
  "Q37813"
  "DOI 10.1111/cobi.70099"

savannaEcologyCoordinate : Traversal.DashiKnowledgeCoordinate
savannaEcologyCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiEcosystemTypologyKnowledgeAuthorityDeweyDoiQidExact.agda"
  "savanna as ecological environment"
  "577.4 — grassland ecology, explicitly including savanna ecology and tropical grassland ecology"
  "Q42320"
  "DOI 10.1111/cobi.70099"

savannaManagementCoordinate : Traversal.DashiKnowledgeCoordinate
savannaManagementCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiEcosystemTypologyKnowledgeAuthorityDeweyDoiQidExact.agda"
  "savanna / grassland as a societal management consumer"
  "333.74 — management of grasslands by society; use is consumer-specific, not an alternative ecological truth value"
  "Q42320"
  "Tiwi Land Council, Tiwi Islands Indigenous Protected Area Plan of Management 2023-2033; DOI not required for primary institutional source"

savannaEcologyToManagement : Traversal.DashiFirstLinkEdge
savannaEcologyToManagement = Traversal.dashi-first-link-edge
  savannaEcologyCoordinate savannaManagementCoordinate Traversal.crossPollinatesWith
  Traversal.canonicalDashiFirstLinkPolicy
  "same savanna identity can participate in distinct ecology and management classification consumers; neither Dewey placement creates the other"
  true

------------------------------------------------------------------------
-- Primary source attribution.
------------------------------------------------------------------------

data EcosystemTypologySourceRole : Set where
  primaryCollaborativeEcosystemClassificationStudy
  primaryInstitutionalManagementSource : EcosystemTypologySourceRole

record EcosystemTypologyAttributedSource : Set where
  constructor ecosystem-typology-attributed-source
  field
    authorsOrInstitution : String
    title : String
    publicationOrInstitution : String
    year : Nat
    stableIdentifier : String
    role : EcosystemTypologySourceRole
    boundedClaim : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner
    ownerRemainsExternal : claimOwner ≡ Attribution.externalSourceOwner

open EcosystemTypologyAttributedSource public

youngEtAl2025 : EcosystemTypologyAttributedSource
youngEtAl2025 = ecosystem-typology-attributed-source
  "Alys R. Young; Hugh F. Davies; Margaret L. Ayre; Alana Brekelmans; Brett A. Bryan; Jane Elith; Kate Hadden; Mavis Kerinaiua; David A. Keith; Donna L. Lewis; Kinjia M. Munkara-Murray; Sarah Ryan; Michaela Spencer; Emily Nicholson"
  "Applying the IUCN Global Ecosystem Typology to classify, describe, and map ecosystems based on regional data and Indigenous knowledge"
  "Conservation Biology 39(6):e70099"
  2025
  "DOI 10.1111/cobi.70099; PMID 40641149; PMCID PMC12658940"
  primaryCollaborativeEcosystemClassificationStudy
  "Primary Tiwi Islands ecosystem-classification and mapping study. It synthesises existing scientific information, field examples and knowledge shared by Tiwi people with relevant environmental knowledge and authority to share it; defines 14 ecosystem types and maps them using Landsat-9 and environmental variables."
  "A scientific ecosystem inventory is not Tiwi Country itself; consultation does not make every consulted knowledge authority a named scientific author; named scientific authorship does not create universal Country authority; the random-forest map does not exhaust Tiwi knowledge or management practice."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner refl

tiwiManagementPlan : EcosystemTypologyAttributedSource
tiwiManagementPlan = ecosystem-typology-attributed-source
  "Tiwi Land Council"
  "Tiwi Islands Indigenous Protected Area Plan of Management 2023-2033"
  "Tiwi Land Council / Tiwi Islands Indigenous Protected Area"
  2025
  "Primary institutional plan, April 2025 edition"
  primaryInstitutionalManagementSource
  "Primary institutional management carrier for Tiwi priorities, threat management and local management targets; retained separately from scientific ecosystem classification."
  "Institutional planning does not become a controlled ecological experiment, and an external scientific DOI does not create management mandate or Country authority."
  Attribution.primaryInstitutionalRecord Attribution.externalSourceOwner refl

------------------------------------------------------------------------
-- Local ecosystem names remain local objects.  Generic QIDs can nominate
-- external search / alignment but do not erase local language or functional
-- classification.
------------------------------------------------------------------------

data TiwiEcosystemType : Set where
  wartaEucalyptOpenForestSavanna
  wartaEucalyptMixedSpeciesSavanna
  muriyiniTreelessPlains
  yawurlamaWetRainforest
  yawurlamaDryRainforest
  punkaringaMelaleucaSavanna
  turringiyaGrasslandSedgelandWetland
  mirriparingaPamparingaMangrove
  yartiCoastalSaltmarsh
  kurlimipitiPungamparnaSandDunes
  tingataSandyShoreline
  tingataRockyShoreline
  urbanModified
  plantation : TiwiEcosystemType

record LocalGlobalEcosystemAlignment : Set where
  constructor local-global-ecosystem-alignment
  field
    localType : TiwiEcosystemType
    localNameReference : String
    genericQidReference : String
    globalTypologyReference : String
    alignmentStatus : String
    sameMeaningClaimed : Bool
    knowledgeAuthorityReference : String
    scientificSource : EcosystemTypologyAttributedSource
    dashiAlignmentOwner : Attribution.ClaimOwner
    dashiOwnsAlignmentOnly : dashiAlignmentOwner ≡ Attribution.dashiFormalisationOwner

open LocalGlobalEcosystemAlignment public

canonicalSavannaAlignment : LocalGlobalEcosystemAlignment
canonicalSavannaAlignment = local-global-ecosystem-alignment
  wartaEucalyptOpenForestSavanna
  "Young et al. 2025 type 1: warta"
  "Q42320"
  "IUCN Global Ecosystem Typology functional alignment supplied by Young et al. 2025"
  "generic savanna concept is an external navigation coordinate; local Tiwi type retains local name, biota, process and threat description"
  false
  "Tiwi knowledge-authority consultation/provenance retained by source; no universal authority inferred"
  youngEtAl2025 Attribution.dashiFormalisationOwner refl

canonicalWetlandAlignment : LocalGlobalEcosystemAlignment
canonicalWetlandAlignment = local-global-ecosystem-alignment
  turringiyaGrasslandSedgelandWetland
  "Young et al. 2025 type 7: turringiya"
  "Q170321"
  "IUCN Global Ecosystem Typology functional alignment supplied by Young et al. 2025"
  "generic wetland QID does not identify the local turringiya ecosystem or its Tiwi knowledge content"
  false
  "local knowledge provenance retained separately from generic wetland identity"
  youngEtAl2025 Attribution.dashiFormalisationOwner refl

------------------------------------------------------------------------
-- The paper's scientific map is one observation/model fibre, not the whole
-- situated LES/Country object.
------------------------------------------------------------------------

record TiwiEcosystemMapReceipt : Set where
  constructor tiwi-ecosystem-map-receipt
  field
    source : EcosystemTypologyAttributedSource
    numberOfEcosystemTypes : Nat
    fieldExampleLocationsRetained : Bool
    landsat9Retained : Bool
    environmentalVariablesRetained : Bool
    randomForestMappingRetained : Bool
    reportedOverallAccuracyReference : String
    scientificMapExhaustsTiwiKnowledge : Bool
    mapCreatesCountryAuthority : Bool
    globalTypologyCreatesLocalIdentity : Bool

open TiwiEcosystemMapReceipt public

canonicalTiwiEcosystemMapReceipt : TiwiEcosystemMapReceipt
canonicalTiwiEcosystemMapReceipt = tiwi-ecosystem-map-receipt
  youngEtAl2025 14 true true true true
  "Young et al. 2025 reports overall map accuracy 83.86%; class-specific errors remain part of the source boundary"
  false false false

------------------------------------------------------------------------
-- BIDI implications: local knowledge can reveal distinctions absent from a
-- coarse global inventory; a global classification can nominate comparison
-- and monitoring obligations without subsuming the local authority surface.
------------------------------------------------------------------------

data GenericQidEqualsLocalEcosystem : Set where
data DeweyClassCreatesSemanticParent : Set where
data ScientificMapEqualsCountry : Set where
data ScientificAuthorshipCreatesCountryAuthority : Set where
data ConsultationCreatesScientificAuthorship : Set where
data GlobalTypologyExhaustsLocalKnowledge : Set where
data SameQidRequiresSingleDeweyClass : Set where
data EcosystemClassificationCreatesThreatEffect : Set where
data ThreatListingCreatesManagementOutcome : Set where

genericQidDoesNotEqualLocalEcosystem : GenericQidEqualsLocalEcosystem → ⊥
genericQidDoesNotEqualLocalEcosystem ()

deweyDoesNotCreateSemanticParent : DeweyClassCreatesSemanticParent → ⊥
deweyDoesNotCreateSemanticParent ()

scientificMapDoesNotEqualCountry : ScientificMapEqualsCountry → ⊥
scientificMapDoesNotEqualCountry ()

scientificAuthorshipDoesNotCreateCountryAuthority : ScientificAuthorshipCreatesCountryAuthority → ⊥
scientificAuthorshipDoesNotCreateCountryAuthority ()

consultationDoesNotCreateScientificAuthorship : ConsultationCreatesScientificAuthorship → ⊥
consultationDoesNotCreateScientificAuthorship ()

globalTypologyDoesNotExhaustLocalKnowledge : GlobalTypologyExhaustsLocalKnowledge → ⊥
globalTypologyDoesNotExhaustLocalKnowledge ()

sameQidDoesNotRequireSingleDeweyClass : SameQidRequiresSingleDeweyClass → ⊥
sameQidDoesNotRequireSingleDeweyClass ()

ecosystemClassificationDoesNotCreateThreatEffect : EcosystemClassificationCreatesThreatEffect → ⊥
ecosystemClassificationDoesNotCreateThreatEffect ()

threatListingDoesNotCreateManagementOutcome : ThreatListingCreatesManagementOutcome → ⊥
threatListingDoesNotCreateManagementOutcome ()

------------------------------------------------------------------------
-- Snowball acquisition/payment: source/QID/Dewey/global-typology acquisition
-- can proceed out of order.  Payment still requires local-type identity,
-- provenance/authority, model validation and consumer-specific empirical edge.
------------------------------------------------------------------------

record EcosystemTypologyAcquisitionState : Set where
  constructor ecosystem-typology-acquisition-state
  field
    Young2025PrimaryAcquired : Bool
    TiwiManagementPlanAcquired : Bool
    ecosystemQidAcquired : Bool
    savannaQidAcquired : Bool
    wetlandQidAcquired : Bool
    mangroveQidAcquired : Bool
    plantationQidAcquired : Bool
    dewey577Acquired : Bool
    dewey5774Acquired : Bool
    dewey33374Acquired : Bool
    localTiwiNamesAcquired : Bool
    globalTypologyMappingAcquired : Bool
    mapValidationAcquired : Bool
    knowledgeAuthorityProvenanceAcquired : Bool
    outOfOrderEvidenceRetained : Bool

record EcosystemTypologyPaymentState : Set where
  constructor ecosystem-typology-payment-state
  field
    primarySourceIdentityPaid : Bool
    exactAuthorshipPaid : Bool
    sourceRolePaid : Bool
    genericQidIdentityPaid : Bool
    localEcosystemIdentityPaid : Bool
    localGlobalAlignmentPaid : Bool
    DeweyConsumerClassificationPaid : Bool
    knowledgeAuthorityProvenancePaid : Bool
    scientificMapMethodPaid : Bool
    mapValidationPaid : Bool
    threatEffectPaid : Bool
    managementOutcomePaid : Bool
    CountryAuthorityPaid : Bool
    firstUnpaidGate : String

snowballAcquisitionDoesNotAdvanceEcosystemTypologyPayment :
  EcosystemTypologyAcquisitionState → EcosystemTypologyPaymentState → EcosystemTypologyPaymentState
snowballAcquisitionDoesNotAdvanceEcosystemTypologyPayment _ payment = payment

firstUnpaidEmpiricalDiscriminator : String
firstUnpaidEmpiricalDiscriminator = MultiDriver.firstUnpaidEmpiricalDiscriminator

firstUnpaidManagementOutcomeDiscriminator : String
firstUnpaidManagementOutcomeDiscriminator = MultiDriver.firstUnpaidManagementOutcomeDiscriminator

firstUnpaidTypologyToMechanismDiscriminator : String
firstUnpaidTypologyToMechanismDiscriminator =
  "For each Tiwi ecosystem type, same-carrier receipt connecting mapped/classified ecosystem identity to measured fire/herbivore/predator/native-fauna mechanism rather than importing threat effects from the generic class"

countryAuthorityBoundary : CountryAuthority.CountryCommunityKnowledgeAuthorityBridgeReceipt
countryAuthorityBoundary = CountryAuthority.canonicalCountryCommunityKnowledgeAuthorityBridgeReceipt

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

traversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
traversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary
