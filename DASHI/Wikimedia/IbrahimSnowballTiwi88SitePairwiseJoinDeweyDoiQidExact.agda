module DASHI.Wikimedia.IbrahimSnowballTiwi88SitePairwiseJoinDeweyDoiQidExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballTiwiSame88SiteMultiDriverPredatorBidiExact as Same88
import DASHI.Wikimedia.IbrahimSnowballTiwiBidiPrimarySourceDoiAttributionLedgerExact as Ledger

------------------------------------------------------------------------
-- PAIRWISE SAME-88-SITE JOIN
--
-- The prior owner correctly refused to say that *every* derived analysis has
-- identical rows/samples.  Primary methods now let us pay a narrower claim:
-- Davies 2017, Davies 2020 and Penton 2021 explicitly reuse the 2015 Melville
-- 88-site survey network.  Pairwise site-set identity is stronger than merely
-- same island/network, but still weaker than row identity, sampling-unit
-- identity, joint-model identity or causal mediation.
------------------------------------------------------------------------

ecologicalDisturbanceQid : Identity.ExternalIdentityDemand
ecologicalDisturbanceQid = Identity.mkOptionalIdentityDemand
  "Tiwi 88-site pairwise join" "ecological-process identity"
  "ecological disturbance" Identity.wikidataQid
  (Identity.verified "Q966490" "Wikidata ecological-disturbance concept verified 2026-09-11; concept identity does not establish a local disturbance measurement")

herbivoryQid : Identity.ExternalIdentityDemand
herbivoryQid = Identity.mkOptionalIdentityDemand
  "Tiwi 88-site pairwise join" "ecological-process identity"
  "herbivory" Identity.wikidataQid
  (Identity.verified "Q45874067" "Wikidata herbivory concept verified 2026-09-11; identity does not establish feral-herbivore pressure")

grazingQid : Identity.ExternalIdentityDemand
grazingQid = Identity.mkOptionalIdentityDemand
  "Tiwi 88-site pairwise join" "feeding-process identity"
  "grazing" Identity.wikidataQid
  (Identity.verified "Q85764397" "Wikidata grazing-behaviour concept verified 2026-09-11; not a site-level grazing intensity receipt")

waterBuffaloQid : Identity.ExternalIdentityDemand
waterBuffaloQid = Identity.mkOptionalIdentityDemand
  "Tiwi 88-site pairwise join" "taxon identity"
  "Bubalus bubalis / water buffalo" Identity.wikidataQid
  (Identity.verified "Q42710" "Wikidata water-buffalo taxon verified 2026-09-11; introduced/feral Melville status remains empirical")

horseQid : Identity.ExternalIdentityDemand
horseQid = Identity.mkOptionalIdentityDemand
  "Tiwi 88-site pairwise join" "taxon identity"
  "Equus caballus / domestic or feral horse" Identity.wikidataQid
  (Identity.verified "Q10758650" "Wikidata Equus caballus taxon verified 2026-09-11; local feral status remains empirical")

same88PairwiseCoordinate : Traversal.DashiKnowledgeCoordinate
same88PairwiseCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwi88SitePairwiseJoinDeweyDoiQidExact.agda"
  "Melville 2015 pairwise same-88-site disturbance / cat / shrub / mammal carrier"
  "577.4 — savanna ecology; 591.7 — animal ecology; Dewey is classification only"
  "Q966490; Q45874067; Q85764397; Q42710; Q10758650; Q146; Q303877"
  "DOI 10.1111/ddi.12522; DOI 10.1071/WR19198; DOI 10.3389/fevo.2021.739550"

record PairwisePrimarySource : Set where
  constructor pairwise-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    carrierStatement : String
    boundedClaim : String
    excludedPromotion : String
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner

open PairwisePrimarySource public

davies2017 : PairwisePrimarySource
davies2017 = pairwise-primary-source
  "Hugh F. Davies; Michael A. McCarthy; Ronald S. C. Firth; John C. Z. Woinarski; Graeme R. Gillespie; Alan N. Andersen; Hayley M. Geyle; Emily Nicholson; Brett P. Murphy"
  "Top-down control of species distributions: feral cats driving the regional extinction of a threatened rodent in northern Australia"
  "Diversity and Distributions 23(3):272-283"
  2017
  "DOI 10.1111/ddi.12522"
  "In 2015, 88 Melville savanna sites were surveyed; 82 used both live- and camera-trapping and six camera-trapping only."
  "Pays site-network identity, shrub-density/cat-detection/rabbit-rat occupancy-demography evidence within this study."
  "Does not prove fire or herbivore causal mediation through shrub structure."
  Attribution.externalSourceOwner refl

davies2020 : PairwisePrimarySource
davies2020 = pairwise-primary-source
  "Hugh F. Davies; Stefan W. Maier; Brett P. Murphy"
  "Feral cats are more abundant under severe disturbance regimes in an Australian tropical savanna"
  "Wildlife Research 47(8):624-632"
  2020
  "DOI 10.1071/WR19198"
  "Analyses the existing 2015 Melville camera-trap data from 88 sites against field- and remotely-derived biophysical variables."
  "Pays severe-fire-frequency and feral-herbivore-activity associations with cat activity/abundance on the 88-site carrier."
  "Association and authors' mechanistic interpretation do not prove fire->understorey or herbivore->understorey mediation."
  Attribution.externalSourceOwner refl

penton2021 : PairwisePrimarySource
penton2021 = pairwise-primary-source
  "Cara E. Penton; Hugh F. Davies; Ian J. Radford; Leigh-Ann Woolley; Tiwi Land Rangers; Brett P. Murphy"
  "A Hollow Argument: Understory Vegetation and Disturbance Determine Abundance of Hollow-Dependent Mammals in an Australian Tropical Savanna"
  "Frontiers in Ecology and Evolution 9:739550"
  2021
  "DOI 10.3389/fevo.2021.739550"
  "Explicitly reuses the 2015 camera-trap surveys at 88 Melville sites from Davies et al. 2017."
  "Pays pairwise reuse of the 88-site mammal camera carrier and species-specific shrub/disturbance associations; Tiwi Land Rangers remain named collective authors."
  "Does not make hollow, shrub, fire, herbivore or cat effects interchangeable and does not create complete mediation."
  Attribution.externalSourceOwner refl

------------------------------------------------------------------------
-- Pairwise identity can be paid without global identity.
------------------------------------------------------------------------

record Pairwise88SiteJoinReceipt : Set where
  constructor pairwise-88-site-join-receipt
  field
    Davies2017SiteSetIs88 : Bool
    Davies2020SiteSetIsExisting2015_88 : Bool
    Penton2021ReusesDavies2017_88 : Bool
    Davies2017Davies2020PairwiseSiteSetPaid : Bool
    Davies2017Penton2021PairwiseSiteSetPaid : Bool
    allThreeShare2015_88SiteCarrierFamilyPaid : Bool
    exactRowIdentityAcrossAllAnalysesPaid : Bool
    exactSamplingUnitIdentityPaid : Bool
    sameResponseVariablePaid : Bool
    sameModelPaid : Bool
    causalMediationPaid : Bool

open Pairwise88SiteJoinReceipt public

canonicalPairwise88SiteJoinReceipt : Pairwise88SiteJoinReceipt
canonicalPairwise88SiteJoinReceipt = pairwise-88-site-join-receipt
  true true true true true true
  false false false false false

------------------------------------------------------------------------
-- Consumer vector: no scalar 'disturbance' coordinate may flatten fire,
-- herbivory/grazing, shrub structure and predator state.
------------------------------------------------------------------------

data LocalDriverCoordinate : Set where
  severeFireFrequency
  feralHerbivoreActivity
  shrubDensity
  catActivity
  catAbundance
  rabbitRatOccupancy
  rabbitRatLocalExtinction : LocalDriverCoordinate

record PairwiseMultiDriverBidiFrontier : Set where
  constructor pairwise-multi-driver-bidi-frontier
  field
    siteCarrierPaid : Bool
    severeFireToCatAssociationPaid : Bool
    herbivoreToCatAssociationPaid : Bool
    shrubToRabbitRatAssociationPaid : Bool
    catToRabbitRatDemographyPaid : Bool
    fireToShrubCausalStepPaid : Bool
    herbivoreToShrubCausalStepPaid : Bool
    shrubToCatCausalStepPaid : Bool
    jointMediationPaid : Bool

open PairwiseMultiDriverBidiFrontier public

canonicalPairwiseMultiDriverBidiFrontier : PairwiseMultiDriverBidiFrontier
canonicalPairwiseMultiDriverBidiFrontier = pairwise-multi-driver-bidi-frontier
  true true true true true
  false false false false

------------------------------------------------------------------------
-- WrongType / provenance firewalls.
------------------------------------------------------------------------

data Same88MeansSameRow : Set where
data PairwiseSiteIdentityMeansMediation : Set where
data DisturbanceQidMeansLocalDisturbance : Set where
data HerbivoryQidMeansFeralHerbivorePressure : Set where
data GrazingQidMeansMeasuredGrazingIntensity : Set where
data TaxonQidMeansLocalFeralPopulation : Set where
data DOISetMeansJointModel : Set where
data DeweyMeansSemanticParent : Set where
data AcquisitionCreatesPayment : Set where

same88DoesNotMeanSameRow : Same88MeansSameRow → ⊥
same88DoesNotMeanSameRow ()

pairwiseSiteIdentityDoesNotCreateMediation : PairwiseSiteIdentityMeansMediation → ⊥
pairwiseSiteIdentityDoesNotCreateMediation ()

disturbanceQidDoesNotMeanLocalDisturbance : DisturbanceQidMeansLocalDisturbance → ⊥
disturbanceQidDoesNotMeanLocalDisturbance ()

herbivoryQidDoesNotMeanFeralHerbivorePressure : HerbivoryQidMeansFeralHerbivorePressure → ⊥
herbivoryQidDoesNotMeanFeralHerbivorePressure ()

grazingQidDoesNotMeanMeasuredIntensity : GrazingQidMeansMeasuredGrazingIntensity → ⊥
grazingQidDoesNotMeanMeasuredIntensity ()

taxonQidDoesNotMeanLocalFeralPopulation : TaxonQidMeansLocalFeralPopulation → ⊥
taxonQidDoesNotMeanLocalFeralPopulation ()

doiSetDoesNotMeanJointModel : DOISetMeansJointModel → ⊥
doiSetDoesNotMeanJointModel ()

deweyDoesNotMeanSemanticParent : DeweyMeansSemanticParent → ⊥
deweyDoesNotMeanSemanticParent ()

acquisitionDoesNotCreatePayment : AcquisitionCreatesPayment → ⊥
acquisitionDoesNotCreatePayment ()

------------------------------------------------------------------------
-- Snowball: acquisition can establish pairwise carrier identity out of order;
-- payment remains blocked on the causal understorey steps.
------------------------------------------------------------------------

record PairwiseJoinAcquisitionState : Set where
  constructor pairwise-join-acquisition-state
  field
    Davies2017Acquired : Bool
    Davies2020Acquired : Bool
    Penton2021Acquired : Bool
    disturbanceQidAcquired : Bool
    herbivoryQidAcquired : Bool
    grazingQidAcquired : Bool
    buffaloQidAcquired : Bool
    horseQidAcquired : Bool
    pairwiseCarrierEvidenceAcquired : Bool
    outOfOrderEvidenceRetained : Bool

record PairwiseJoinPaymentState : Set where
  constructor pairwise-join-payment-state
  field
    primarySourceIdentityPaid : Bool
    attributionPaid : Bool
    QidIdentityPaid : Bool
    DeweyCoordinatePaid : Bool
    pairwiseSiteCarrierPaid : Bool
    exactRowJoinPaid : Bool
    fireToShrubPaid : Bool
    herbivoreToShrubPaid : Bool
    shrubToCatPaid : Bool
    jointMediationPaid : Bool
    firstUnpaidGate : String

snowballAcquisitionDoesNotAdvancePairwiseJoinPayment :
  PairwiseJoinAcquisitionState → PairwiseJoinPaymentState → PairwiseJoinPaymentState
snowballAcquisitionDoesNotAdvancePairwiseJoinPayment _ payment = payment

firstUnpaidGate : String
firstUnpaidGate =
  "Within the paid 2015 Melville 88-site carrier, identify a primary analysis or join that measures fire/herbivore pressure -> shrub/understorey state -> cat activity at compatible site/time resolution without substituting association for mediation"

priorSame88Boundary :
  Same88.Same88AcquisitionState → Same88.Same88PaymentState → Same88.Same88PaymentState
priorSame88Boundary = Same88.snowballAcquisitionDoesNotAdvanceSame88Payment

ledgerFirstUnpaid : String
ledgerFirstUnpaid = Ledger.firstUnpaidEmpiricalDiscriminator

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

traversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
traversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary
