module DASHI.Wikimedia.IbrahimSnowballTiwiMultiDriverPredatorAccessDeweyDoiQidExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballTiwiBidiPrimarySourceDoiAttributionLedgerExact as Ledger

------------------------------------------------------------------------
-- TIWI MULTI-DRIVER PREDATOR-ACCESS BIDI SNOWBALL
--
-- Fire is not treated as the sole upstream driver.  Melville observations
-- support a consumer that depends jointly on severe-fire frequency and feral-
-- herbivore disturbance, while megaherbivore trails provide a second local
-- predator-access carrier.  These sources narrow the mechanism but do not pay
-- the still-missing experimental fire -> shrub/understorey-density edge.
------------------------------------------------------------------------

feralCatQid : Identity.ExternalIdentityDemand
feralCatQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver predator-access continuation" "external ecological identity"
  "feral cat" Identity.wikidataQid
  (Identity.verified "Q2404562" "Wikidata feral-cat concept inspected 2026-09-11; distinct from generic cat Q146 and from any local Melville population")

waterBuffaloQid : Identity.ExternalIdentityDemand
waterBuffaloQid = Ledger.waterBuffaloQid

horseQid : Identity.ExternalIdentityDemand
horseQid = Ledger.horseQid

dingoQid : Identity.ExternalIdentityDemand
dingoQid = Ledger.dingoQid

severeDisturbanceQid : Identity.ExternalIdentityDemand
severeDisturbanceQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver predator-access continuation" "external ecological-process identity"
  "severe ecological disturbance regime" Identity.wikidataQid
  (Identity.unresolved "No safely verified exact Wikidata concept item promoted; constituent fire/herbivore identities remain separate")

multiDriverCoordinate : Traversal.DashiKnowledgeCoordinate
multiDriverCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiMultiDriverPredatorAccessDeweyDoiQidExact.agda"
  "Tiwi/Melville severe-disturbance predator-access consumer"
  "577.4 — savanna ecology; classification coordinate only"
  "Q2404562; Q42710; Q10758650"
  "DOI 10.1071/WR19198; DOI 10.1071/PC20088; DOI 10.1002/ece3.71622"

predatorDensityCoordinate : Traversal.DashiKnowledgeCoordinate
predatorDensityCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiMultiDriverPredatorAccessDeweyDoiQidExact.agda"
  "feral-cat activity / density consumer"
  "577.4 — savanna ecology; mammal-taxonomy Dewey remains a separate coordinate"
  "Q2404562"
  "DOI 10.1071/WR19198; DOI 10.1071/PC20088"

multiDriverSupportsPredatorConsumer : Traversal.DashiFirstLinkEdge
multiDriverSupportsPredatorConsumer = Traversal.dashi-first-link-edge
  multiDriverCoordinate predatorDensityCoordinate Traversal.supportedBy
  Traversal.canonicalDashiFirstLinkPolicy
  "Melville primary studies associate cat activity/density with severe-fire and feral-herbivore disturbance; this edge is source-bounded and is not complete mediation"
  true

data MultiDriverSourceRole : Set where
  MelvilleDisturbanceCatActivity
  TiwiIslandCatDensityContrast
  TiwiNativeMammalDensityContrast
  MelvilleMegaherbivoreTrailPredatorAccess : MultiDriverSourceRole

record MultiDriverPrimarySource : Set where
  constructor multi-driver-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    role : MultiDriverSourceRole
    boundedClaim : String
    excludedPromotion : String
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner

open MultiDriverPrimarySource public

daviesMaierMurphy2020 : MultiDriverPrimarySource
daviesMaierMurphy2020 = multi-driver-primary-source
  "Hugh F. Davies; Stefan W. Maier; Brett P. Murphy"
  "Feral cats are more abundant under severe disturbance regimes in an Australian tropical savanna"
  "Wildlife Research 47(8):624-632"
  2020
  "DOI 10.1071/WR19198"
  MelvilleDisturbanceCatActivity
  "Primary Melville Island camera-trap study across 88 sites; cat activity and abundance were highest under severe disturbance characterised by high frequencies of severe fire and high feral-herbivore activity."
  "Association does not establish that fire acts only through understorey, does not isolate buffalo from horse effects, and does not pay prey mortality or full mediation."
  Attribution.externalSourceOwner refl

daviesTiwiRangersEtAl2022Cat : MultiDriverPrimarySource
daviesTiwiRangersEtAl2022Cat = multi-driver-primary-source
  "Hugh F. Davies; Tiwi Land Rangers; Matthew W. Rees; Danielle Stokeld; Anna C. Miller; Graeme R. Gillespie; Brett P. Murphy"
  "Variation in feral cat density between two large adjacent islands in Australia's monsoon tropics"
  "Pacific Conservation Biology 28(1):18-24"
  2022
  "DOI 10.1071/PC20088"
  TiwiIslandCatDensityContrast
  "Primary Tiwi Islands spatial capture-recapture study comparing four large camera grids across combinations of fire frequency and feral-herbivore presence; estimated Melville cat density at 0.15 cats per square kilometre and detected no cats on Bathurst grids."
  "Island contrast does not identify one causal driver; absence of herbivores on Bathurst is not by itself a randomized herbivore-removal experiment. Tiwi Land Rangers collective authorship is retained exactly."
  Attribution.externalSourceOwner refl

daviesTiwiRangersEtAl2022Mammals : MultiDriverPrimarySource
daviesTiwiRangersEtAl2022Mammals = multi-driver-primary-source
  "Hugh F. Davies; Tiwi Land Rangers; Emily Nicholson; Brett P. Murphy"
  "Northern brown bandicoot (Isoodon macrourus) and common brushtail possum (Trichosurus vulpecula) density on the Tiwi Islands: insights and implications"
  "Pacific Conservation Biology 28(3):224-230"
  2022
  "DOI 10.1071/PC21020"
  TiwiNativeMammalDensityContrast
  "Primary Tiwi Islands spatial capture-recapture study at four sites spanning different fire-frequency, feral-cat-density and feral-herbivore contexts; consumer is native-mammal density, not predator density."
  "Four-site density contrasts do not isolate causal effects of fire, cats or herbivores and cannot be flattened into a single disturbance score. Tiwi Land Rangers collective authorship is retained exactly."
  Attribution.externalSourceOwner refl

neaveTiwiRangersEtAl2025 : MultiDriverPrimarySource
neaveTiwiRangersEtAl2025 = multi-driver-primary-source
  "Georgina Neave; Brett P. Murphy; Tiwi Rangers; Hugh F. Davies"
  "Exotic Megaherbivores as Ecosystem Engineers in Australian Savannas: Do They Facilitate Predator Movement?"
  "Ecology and Evolution 15(7):e71622"
  2025
  "DOI 10.1002/ece3.71622; Dryad DOI 10.5061/dryad.0zpc86776"
  MelvilleMegaherbivoreTrailPredatorAccess
  "Primary Melville Island paired-camera study at 52 sites; predator detections were substantially elevated on megaherbivore game trails relative to adjacent undisturbed vegetation."
  "Trail use does not equal predation mortality or prove that megaherbivore control benefits native mammals. Tiwi Rangers collective authorship is retained exactly."
  Attribution.externalSourceOwner refl

------------------------------------------------------------------------
-- BIDI state: forward observations and reverse consumer constraints.
------------------------------------------------------------------------

record MultiDriverPredatorAccessFrontier : Set where
  constructor multi-driver-predator-access-frontier
  field
    fireFrequencyEvidence : Bool
    severeFireEvidence : Bool
    feralHerbivoreEvidence : Bool
    catActivityEvidence : Bool
    catDensityEvidence : Bool
    gameTrailPredatorAccessEvidence : Bool
    nativeMammalDensityEvidence : Bool
    sameIslandCarrier : Bool
    sameExactSitesAcrossAllSources : Bool
    fireToUnderstoreyCausalEdgePaid : Bool
    herbivoreToUnderstoreyCausalEdgePaid : Bool
    understoreyToPredatorAccessPaid : Bool
    predatorAccessToPreyDemographyPaid : Bool
    completeJointMediationPaid : Bool
    dashiInferenceOwner : Attribution.ClaimOwner
    dashiOwnsInferenceOnly : dashiInferenceOwner ≡ Attribution.dashiInferenceOwner

open MultiDriverPredatorAccessFrontier public

canonicalMultiDriverFrontier : MultiDriverPredatorAccessFrontier
canonicalMultiDriverFrontier = multi-driver-predator-access-frontier
  true true true true true true true true
  false false false false false false
  Attribution.dashiInferenceOwner refl

record MultiDriverSnowballAcquisitionState : Set where
  constructor multi-driver-snowball-acquisition-state
  field
    WR19198Acquired : Bool
    PC20088Acquired : Bool
    PC21020Acquired : Bool
    ECE371622Acquired : Bool
    feralCatQidAcquired : Bool
    waterBuffaloQidAcquired : Bool
    horseQidAcquired : Bool
    dingoQidAcquired : Bool
    severeDisturbanceQidAcquired : Bool
    laterEvidenceRetainedOutOfOrder : Bool

record MultiDriverSnowballPaymentState : Set where
  constructor multi-driver-snowball-payment-state
  field
    sourceIdentityPaid : Bool
    sourceRoleAttributionPaid : Bool
    exactSitePaid : Bool
    exactTimeWindowPaid : Bool
    exactDriverStatePaid : Bool
    exactPredatorConsumerPaid : Bool
    exactPreyConsumerPaid : Bool
    crossSourceSiteJoinPaid : Bool
    fireUnderstoreyPaid : Bool
    herbivoreUnderstoreyPaid : Bool
    understoreyPredatorPaid : Bool
    predatorPreyPaid : Bool
    jointMediationPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

snowballAcquisitionDoesNotAdvanceMultiDriverPayment :
  MultiDriverSnowballAcquisitionState → MultiDriverSnowballPaymentState → MultiDriverSnowballPaymentState
snowballAcquisitionDoesNotAdvanceMultiDriverPayment _ payment = payment

data DisturbanceAssociationMeansMediation : Set where
data IslandContrastMeansHerbivoreCausality : Set where
data PredatorTrailUseMeansPreyMortality : Set where
data NativeMammalDensityMeansDriverIdentity : Set where
data QidCreatesLocalObservation : Set where
data DoiArrayCreatesJointMechanism : Set where
data DeweyCreatesSemanticParent : Set where

disturbanceAssociationDoesNotCreateMediation : DisturbanceAssociationMeansMediation → ⊥
disturbanceAssociationDoesNotCreateMediation ()

islandContrastDoesNotCreateHerbivoreCausality : IslandContrastMeansHerbivoreCausality → ⊥
islandContrastDoesNotCreateHerbivoreCausality ()

predatorTrailUseDoesNotCreatePreyMortality : PredatorTrailUseMeansPreyMortality → ⊥
predatorTrailUseDoesNotCreatePreyMortality ()

nativeMammalDensityDoesNotIdentifyDriver : NativeMammalDensityMeansDriverIdentity → ⊥
nativeMammalDensityDoesNotIdentifyDriver ()

qidDoesNotCreateLocalObservation : QidCreatesLocalObservation → ⊥
qidDoesNotCreateLocalObservation ()

doiArrayDoesNotCreateJointMechanism : DoiArrayCreatesJointMechanism → ⊥
doiArrayDoesNotCreateJointMechanism ()

deweyDoesNotCreateSemanticParent : DeweyCreatesSemanticParent → ⊥
deweyDoesNotCreateSemanticParent ()

firstUnpaidEmpiricalDiscriminator : String
firstUnpaidEmpiricalDiscriminator =
  "Exact Tiwi/Melville measured vegetation-structure response that separates fire severity/frequency from feral-herbivore disturbance on a carrier joinable to cat and native-mammal consumers"

priorSourceLedgerBoundary : AttributionSnowball.AttributionSnowballBoundary
priorSourceLedgerBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

traversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
traversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary
