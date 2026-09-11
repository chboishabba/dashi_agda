module DASHI.Wikimedia.IbrahimSnowballTiwiMultiDriverManagementDeweyDoiQidExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballTiwiMegaherbivorePredatorAccessDeweyDoiQidExact as Mega
import DASHI.Wikimedia.IbrahimSnowballTiwiSame88SiteMultiDriverPredatorBidiExact as Same88

------------------------------------------------------------------------
-- TIWI MULTI-DRIVER MANAGEMENT FOLLOW
--
-- Keep empirical ecology and Indigenous institutional management/governance
-- sources in distinct fibres.  A primary institutional plan may own priorities,
-- targets and recorded community statements; it does not become a controlled
-- ecological experiment.  Conversely, an empirical DOI does not create a
-- management mandate or Country authority.
------------------------------------------------------------------------

waterBuffaloIdentity = Mega.waterBuffaloQid
horseIdentity = Mega.horseQid
pigIdentity = Mega.pigQid
dingoIdentity = Mega.dingoQid
herbivoryIdentity = Mega.herbivoryQid
gameTrailIdentity = Mega.gameTrailQid

tiwiLandCouncilQid : Identity.ExternalIdentityDemand
tiwiLandCouncilQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver management snowball" "organisation identity"
  "Tiwi Land Council" Identity.wikidataQid
  (Identity.unresolved "No safely verified direct Tiwi Land Council Wikidata item promoted in this tranche; organisation identity is not inferred from Tiwi people/place QIDs")

indigenousProtectedAreaQid : Identity.ExternalIdentityDemand
indigenousProtectedAreaQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver management snowball" "management-area concept identity"
  "Indigenous Protected Area / Tiwi Islands IPA" Identity.wikidataQid
  (Identity.unresolved "No exact Tiwi Islands IPA Wikidata item safely verified; generic protected-area concepts are not substituted for the local management object")

------------------------------------------------------------------------
-- Dewey / DOI / source coordinates.
------------------------------------------------------------------------

ecologicalEvidenceCoordinate : Traversal.DashiKnowledgeCoordinate
ecologicalEvidenceCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiMultiDriverManagementDeweyDoiQidExact.agda"
  "Tiwi savanna disturbance / predator-access evidence"
  "577.4 — grassland ecology, including savanna ecology"
  "Q42710; Q10758650; Q58697; Q45874067; Q38584; unresolved game-trail QID"
  "DOI 10.1071/WR19198; DOI 10.1002/ece3.71622; DOI 10.1111/ddi.12522; DOI 10.3389/fevo.2021.739550"

conservationManagementCoordinate : Traversal.DashiKnowledgeCoordinate
conservationManagementCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiMultiDriverManagementDeweyDoiQidExact.agda"
  "Tiwi conservation / management planning"
  "333.72 — conservation and protection of natural resources; management-classification coordinate only"
  "unresolved Tiwi Land Council QID; unresolved exact Tiwi Islands IPA QID"
  "Tiwi Land Council, Tiwi Islands Indigenous Protected Area Plan of Management 2023-2033, April 2025; institutional source has no DOI requirement"

empiricalToManagementCrossPollination : Traversal.DashiFirstLinkEdge
empiricalToManagementCrossPollination = Traversal.dashi-first-link-edge
  ecologicalEvidenceCoordinate conservationManagementCoordinate Traversal.crossPollinatesWith
  Traversal.canonicalDashiFirstLinkPolicy
  "empirical disturbance/predator evidence can inform management reasoning, but does not dictate local priorities, Country authority, targets or intervention choice"
  true

managementToEmpiricalSearchObligation : Traversal.DashiFirstLinkEdge
managementToEmpiricalSearchObligation = Traversal.dashi-first-link-edge
  conservationManagementCoordinate ecologicalEvidenceCoordinate Traversal.crossPollinatesWith
  Traversal.canonicalDashiFirstLinkPolicy
  "management priorities nominate empirical acquisition obligations; institutional priority does not itself prove ecological effect"
  true

------------------------------------------------------------------------
-- Exact source attribution.
------------------------------------------------------------------------

data ManagementSourceRole : Set where
  primaryEmpiricalPublication
  primaryInstitutionalManagementPlan : ManagementSourceRole

record TiwiManagementAttributedSource : Set where
  constructor tiwi-management-attributed-source
  field
    sourceName : String
    sourceTitle : String
    publicationOrInstitution : String
    year : Nat
    stableIdentifier : String
    role : ManagementSourceRole
    boundedClaim : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner
    ownerRemainsExternal : claimOwner ≡ Attribution.externalSourceOwner

open TiwiManagementAttributedSource public

daviesMaierMurphy2020 : TiwiManagementAttributedSource
daviesMaierMurphy2020 = tiwi-management-attributed-source
  "Hugh F. Davies; Stefan W. Maier; Brett P. Murphy"
  "Feral cats are more abundant under severe disturbance regimes in an Australian tropical savanna"
  "Wildlife Research 47(8):624-632"
  2020
  "DOI 10.1071/WR19198"
  primaryEmpiricalPublication
  "Primary Melville 88-site study: cat activity and abundance were highest under severe disturbance regimes characterised by high frequencies of severe fire and high feral-herbivore activity."
  "The authors' understorey-opening mechanism is an interpretation of the observed multi-driver association; it does not by itself pay measured fire->understorey or herbivore->understorey mediation, prey mortality or management benefit."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner refl

neaveMurphyTiwiRangersDavies2025 : TiwiManagementAttributedSource
neaveMurphyTiwiRangersDavies2025 = tiwi-management-attributed-source
  "Georgina Neave; Brett P. Murphy; Tiwi Rangers; Hugh F. Davies"
  "Exotic Megaherbivores as Ecosystem Engineers in Australian Savannas: Do They Facilitate Predator Movement?"
  "Ecology and Evolution 15(7):e71622"
  2025
  "DOI 10.1002/ece3.71622; Dryad DOI 10.5061/dryad.0zpc86776"
  primaryEmpiricalPublication
  "Primary Melville paired-camera evidence at 52 sites showing cats and dingoes were detected more often on megaherbivore game trails than in adjacent vegetation; Tiwi Rangers are named collective authors."
  "Trail use is not predation mortality; predator access is not native-mammal demographic benefit/harm; megaherbivore removal is not experimentally proved here as a conservation outcome."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner refl

tiwiLandCouncilIPAPlan2025 : TiwiManagementAttributedSource
tiwiLandCouncilIPAPlan2025 = tiwi-management-attributed-source
  "Tiwi Land Council"
  "Tiwi Islands Indigenous Protected Area Plan of Management 2023-2033"
  "Tiwi Land Council / Tiwi Islands Indigenous Protected Area"
  2025
  "Primary institutional plan, April 2025 edition; stable institutional PDF title retained"
  primaryInstitutionalManagementPlan
  "Primary Tiwi institutional management source identifying feral buffalo, pigs and horses as a top threat; records targets including reducing buffalo and horse numbers to agreed levels and documents Tiwi Traditional Owner statements about damage to Country, wetlands, vegetation and infrastructure."
  "Institutional/community management priorities and recorded testimony are not controlled ecological-effect estimates, do not manufacture a DOI, and are not replaced by external scientific authorship. Quoted Traditional Owner statements remain distinct from institutional synthesis."
  Attribution.primaryInstitutionalRecord Attribution.externalSourceOwner refl

------------------------------------------------------------------------
-- Consumer-relative management frontier.
------------------------------------------------------------------------

record TiwiMultiDriverManagementFrontier : Set where
  constructor tiwi-multi-driver-management-frontier
  field
    same88FireCatAssociationPaid : Bool
    same88HerbivoreCatAssociationPaid : Bool
    MelvilleTrailPredatorAccessPaid : Bool
    TiwiInstitutionalThreatPriorityPaid : Bool
    TiwiBuffaloHorseReductionTargetPaid : Bool
    fireToUnderstoreyMediationPaid : Bool
    herbivoreToUnderstoreyMediationPaid : Bool
    predatorAccessToMortalityPaid : Bool
    interventionToNativeMammalBenefitPaid : Bool
    wholeCountryAuthorityInferredFromPlan : Bool

open TiwiMultiDriverManagementFrontier public

canonicalTiwiMultiDriverManagementFrontier : TiwiMultiDriverManagementFrontier
canonicalTiwiMultiDriverManagementFrontier = tiwi-multi-driver-management-frontier
  true true true true true
  false false false false false

------------------------------------------------------------------------
-- BIDI / no-promotion boundaries.
------------------------------------------------------------------------

data EmpiricalAssociationCreatesManagementMandate : Set where
data ManagementPriorityCreatesCausalEffect : Set where
data InstitutionalPlanCreatesControlledExperiment : Set where
data DOIRequirementAppliesToInstitutionalPlan : Set where
data OrganisationQidCreatesCountryAuthority : Set where
data SpeciesQidCreatesLocalThreatMagnitude : Set where
data DeweyManagementClassCreatesRecommendation : Set where
data MegaherbivoreRemovalMeansNativeMammalBenefit : Set where
data RecordedTraditionalOwnerStatementMeansScientificEffectEstimate : Set where

empiricalAssociationDoesNotCreateManagementMandate : EmpiricalAssociationCreatesManagementMandate → ⊥
empiricalAssociationDoesNotCreateManagementMandate ()

managementPriorityDoesNotCreateCausalEffect : ManagementPriorityCreatesCausalEffect → ⊥
managementPriorityDoesNotCreateCausalEffect ()

institutionalPlanDoesNotCreateControlledExperiment : InstitutionalPlanCreatesControlledExperiment → ⊥
institutionalPlanDoesNotCreateControlledExperiment ()

doiRequirementDoesNotApplyToInstitutionalPlan : DOIRequirementAppliesToInstitutionalPlan → ⊥
doiRequirementDoesNotApplyToInstitutionalPlan ()

organisationQidDoesNotCreateCountryAuthority : OrganisationQidCreatesCountryAuthority → ⊥
organisationQidDoesNotCreateCountryAuthority ()

speciesQidDoesNotCreateLocalThreatMagnitude : SpeciesQidCreatesLocalThreatMagnitude → ⊥
speciesQidDoesNotCreateLocalThreatMagnitude ()

deweyManagementClassDoesNotCreateRecommendation : DeweyManagementClassCreatesRecommendation → ⊥
deweyManagementClassDoesNotCreateRecommendation ()

megaherbivoreRemovalDoesNotMeanNativeMammalBenefit : MegaherbivoreRemovalMeansNativeMammalBenefit → ⊥
megaherbivoreRemovalDoesNotMeanNativeMammalBenefit ()

recordedTraditionalOwnerStatementDoesNotBecomeScientificEffectEstimate : RecordedTraditionalOwnerStatementMeansScientificEffectEstimate → ⊥
recordedTraditionalOwnerStatementDoesNotBecomeScientificEffectEstimate ()

------------------------------------------------------------------------
-- Snowball: later management evidence can be retained before mechanism gates
-- are paid, and empirical evidence can be retained before local governance
-- targets are acquired.  Neither acquisition direction advances the other.
------------------------------------------------------------------------

record MultiDriverManagementAcquisitionState : Set where
  constructor multi-driver-management-acquisition-state
  field
    Davies2020PrimaryAcquired : Bool
    Neave2025PrimaryAcquired : Bool
    TiwiIPAPlanAcquired : Bool
    buffaloQidAcquired : Bool
    horseQidAcquired : Bool
    pigQidAcquired : Bool
    dingoQidAcquired : Bool
    organisationQidAcquired : Bool
    exactIPAQidAcquired : Bool
    deweyEcologyAcquired : Bool
    deweyConservationAcquired : Bool
    outOfOrderEvidenceRetained : Bool

record MultiDriverManagementPaymentState : Set where
  constructor multi-driver-management-payment-state
  field
    empiricalSourceIdentityPaid : Bool
    institutionalSourceIdentityPaid : Bool
    attributionRolesPaid : Bool
    QidIdentitiesPaid : Bool
    DeweyClassificationPaid : Bool
    empiricalMultiDriverAssociationPaid : Bool
    institutionalPriorityPaid : Bool
    managementTargetPaid : Bool
    causalMediationPaid : Bool
    interventionOutcomePaid : Bool
    CountryAuthorityPaid : Bool
    firstUnpaidGate : String

snowballAcquisitionDoesNotAdvanceManagementPayment :
  MultiDriverManagementAcquisitionState → MultiDriverManagementPaymentState → MultiDriverManagementPaymentState
snowballAcquisitionDoesNotAdvanceManagementPayment _ payment = payment

firstUnpaidEmpiricalDiscriminator : String
firstUnpaidEmpiricalDiscriminator = Same88.firstUnpaidEmpiricalDiscriminator

firstUnpaidMultiDriverDiscriminator : String
firstUnpaidMultiDriverDiscriminator = Same88.firstUnpaidMultiDriverDiscriminator

firstUnpaidManagementOutcomeDiscriminator : String
firstUnpaidManagementOutcomeDiscriminator =
  "Intervention receipt connecting a specified Tiwi fire and/or megaherbivore-management change to measured structural, predator and native-mammal outcomes on the same bounded carrier"

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

traversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
traversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary
