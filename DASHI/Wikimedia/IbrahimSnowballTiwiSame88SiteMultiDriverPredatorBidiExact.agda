module DASHI.Wikimedia.IbrahimSnowballTiwiSame88SiteMultiDriverPredatorBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballTiwiShrubPredationMediationDeweyDoiQidExact as Shrub
import DASHI.Wikimedia.IbrahimSnowballTiwiMegaherbivorePredatorAccessDeweyDoiQidExact as Mega
import DASHI.Wikimedia.IbrahimSnowballTiwiBidiPrimarySourceDoiAttributionLedgerExact as Ledger

------------------------------------------------------------------------
-- SAME-88-SITE MELVILLE BIDI WELD
--
-- The 2015 Melville survey network is reused across several primary analyses.
-- This pays a same-survey-network relation, not automatic row/sample identity
-- and not causal mediation. Fire severity and feral-herbivore activity are
-- treated as distinct upstream drivers of cat activity/abundance.
------------------------------------------------------------------------

herbivoryQid : Identity.ExternalIdentityDemand
herbivoryQid = Identity.mkOptionalIdentityDemand
  "Tiwi same-88-site multi-driver predator BIDI" "ecological-process identity"
  "herbivory" Identity.wikidataQid
  (Identity.verified "Q45874067" "Wikidata herbivory concept verified 2026-09-11; identity does not establish Melville grazing pressure or effect")

catQid : Identity.ExternalIdentityDemand
catQid = Identity.mkOptionalIdentityDemand
  "Tiwi same-88-site multi-driver predator BIDI" "taxon identity"
  "Felis catus / cat" Identity.wikidataQid
  (Identity.verified "Q146" "Wikidata cat identity retained; feral status and Melville activity require empirical receipts")

rabbitRatQid : Identity.ExternalIdentityDemand
rabbitRatQid = Identity.mkOptionalIdentityDemand
  "Tiwi same-88-site multi-driver predator BIDI" "taxon identity"
  "Conilurus penicillatus / brush-tailed rabbit-rat" Identity.wikidataQid
  (Identity.verified "Q303877" "Wikidata taxon identity retained from prior Tiwi snowball")

same88SiteCoordinate : Traversal.DashiKnowledgeCoordinate
same88SiteCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiSame88SiteMultiDriverPredatorBidiExact.agda"
  "Melville 2015 88-site disturbance/predator/mammal survey network"
  "577.4 — savanna ecology; classification coordinate only"
  "Q45874067; Q146; Q303877; Q42710; Q10758650"
  "DOI 10.1111/ddi.12522; DOI 10.1111/aec.12596; DOI 10.1071/WR19198; DOI 10.3389/fevo.2021.739550; DOI 10.1002/ece3.71622"

same88AnimalEcologyCoordinate : Traversal.DashiKnowledgeCoordinate
same88AnimalEcologyCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiSame88SiteMultiDriverPredatorBidiExact.agda"
  "Melville mammal/predator environment consumer"
  "591.7 — animal ecology, animals characteristic of specific environments"
  "Q146; Q303877; Q42710; Q10758650; Q45874067"
  "DOI 10.1071/WR19198; DOI 10.1111/ddi.12522; DOI 10.3389/fevo.2021.739550; DOI 10.1002/ece3.71622"

record Same88SitePrimarySource : Set where
  constructor same-88-site-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    boundedClaim : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner

open Same88SitePrimarySource public

daviesEtAl2020 : Same88SitePrimarySource
daviesEtAl2020 = same-88-site-primary-source
  "Hugh F. Davies; Stefan W. Maier; Brett P. Murphy"
  "Feral cats are more abundant under severe disturbance regimes in an Australian tropical savanna"
  "Wildlife Research 47(8):624-632"
  2020
  "DOI 10.1071/WR19198"
  "Primary Melville analysis of existing 2015 data from 88 sites; feral-cat activity and abundance were highest under severe disturbance regimes characterised by high frequency of severe fire and high feral-herbivore activity."
  "Observational disturbance correlates and authors' mechanism interpretation do not by themselves prove fire->understorey->cat mediation, herbivore->understorey mediation, prey mortality, or management benefit."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner refl

daviesEtAl2018Decline : Same88SitePrimarySource
daviesEtAl2018Decline = same-88-site-primary-source
  "Hugh F. Davies; Michael A. McCarthy; Ronald S. C. Firth; John C. Z. Woinarski; Graeme R. Gillespie; Alan N. Andersen; Willie Rioli; José Puruntatameri; Willie Roberts; Colin Kerinaiua; Vivian Kerinauia; Kim Brooks Womatakimi; Brett P. Murphy"
  "Declining populations in one of the last refuges for threatened mammal species in northern Australia"
  "Austral Ecology 43(5):602-612"
  2018
  "DOI 10.1111/aec.12596"
  "Primary Melville resurvey: 88 sites revisited in 2015, 82 with both live- and camera-trapping, reporting substantial 2000-2002 to 2015 mammal declines and species-specific responses."
  "Population decline does not identify a unique causal driver and does not make all 88 site-level measurements interchangeable across papers."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner refl

------------------------------------------------------------------------
-- Same-network is stronger than same island, weaker than same row/sample.
------------------------------------------------------------------------

data CarrierLevel : Set where
  sameIsland
  sameSurveyNetwork
  sameSiteSet
  sameExactSite
  sameObservationWindow
  sameSample : CarrierLevel

record Same88SiteCrossStudyReceipt : Set where
  constructor same-88-site-cross-study-receipt
  field
    Davies2017Uses88Sites2015 : Bool
    Davies2018Uses88Sites2015 : Bool
    Davies2020UsesExisting88Site2015Data : Bool
    PentonUses2015CameraNetwork : Bool
    sameMelvilleSurveyNetworkPaid : Bool
    same88SiteSetAcrossEveryDerivedAnalysisPaid : Bool
    exactRowIdentityAcrossEveryPaperPaid : Bool
    sameSamplingUnitAcrossEveryPaperPaid : Bool
    sameModelResponseAcrossEveryPaperPaid : Bool

open Same88SiteCrossStudyReceipt public

canonicalSame88SiteCrossStudyReceipt : Same88SiteCrossStudyReceipt
canonicalSame88SiteCrossStudyReceipt = same-88-site-cross-study-receipt
  true true true true true
  false false false false

------------------------------------------------------------------------
-- Multi-driver state: fire-only compression is now explicitly inadequate.
------------------------------------------------------------------------

data DisturbanceDriver : Set where
  severeFireFrequency
  feralHerbivoreActivity
  shrubUnderstoreyState
  gameTrailNetwork : DisturbanceDriver

data ResponseConsumer : Set where
  catActivity
  catAbundance
  rabbitRatOccupancy
  rabbitRatLocalExtinction
  multiTaxonAbundance : ResponseConsumer

record MultiDriverSame88BidiFrontier : Set where
  constructor multi-driver-same-88-bidi-frontier
  field
    severeFireCatAssociationPaid : Bool
    herbivoreCatAssociationPaid : Bool
    shrubRabbitRatAssociationPaid : Bool
    catRabbitRatDemographyPaid : Bool
    gameTrailPredatorAccessPaid : Bool
    sameSurveyNetworkPaid : Bool
    fireToShrubCausalStepPaid : Bool
    herbivoreToShrubCausalStepPaid : Bool
    shrubToCatCausalStepPaid : Bool
    catToRabbitRatCausalStepPaid : Bool
    fullSameSiteMediationPaid : Bool

open MultiDriverSame88BidiFrontier public

canonicalMultiDriverSame88BidiFrontier : MultiDriverSame88BidiFrontier
canonicalMultiDriverSame88BidiFrontier = multi-driver-same-88-bidi-frontier
  true true true true true true
  false false false false false

------------------------------------------------------------------------
-- BIDI no-go results: observed predator/prey patterns force retention of more
-- than one disturbance coordinate; same survey network still cannot manufacture
-- causal composition.
------------------------------------------------------------------------

data FireOnlyRecoversPredatorState : Set where
data HerbivoreOnlyRecoversPredatorState : Set where
data Same88SitesMeansSameRows : Set where
data SameRowsMeansCausalMediation : Set where
data CatAssociationMeansPredationMortality : Set where
data ManagementImplicationMeansBenefit : Set where
data QidMeansLocalMeasurement : Set where
data DOISetMeansJointModel : Set where

data DeweyMeansEcologicalEvidence : Set where

fireOnlyDoesNotRecoverPredatorState : FireOnlyRecoversPredatorState → ⊥
fireOnlyDoesNotRecoverPredatorState ()

herbivoreOnlyDoesNotRecoverPredatorState : HerbivoreOnlyRecoversPredatorState → ⊥
herbivoreOnlyDoesNotRecoverPredatorState ()

same88SitesDoNotCreateSameRows : Same88SitesMeansSameRows → ⊥
same88SitesDoNotCreateSameRows ()

sameRowsDoNotCreateCausalMediation : SameRowsMeansCausalMediation → ⊥
sameRowsDoNotCreateCausalMediation ()

catAssociationDoesNotMeanPredationMortality : CatAssociationMeansPredationMortality → ⊥
catAssociationDoesNotMeanPredationMortality ()

managementImplicationDoesNotMeanBenefit : ManagementImplicationMeansBenefit → ⊥
managementImplicationDoesNotMeanBenefit ()

qidDoesNotMeanLocalMeasurement : QidMeansLocalMeasurement → ⊥
qidDoesNotMeanLocalMeasurement ()

doiSetDoesNotMeanJointModel : DOISetMeansJointModel → ⊥
doiSetDoesNotMeanJointModel ()

deweyDoesNotMeanEcologicalEvidence : DeweyMeansEcologicalEvidence → ⊥
deweyDoesNotMeanEcologicalEvidence ()

------------------------------------------------------------------------
-- Snowball: acquisition may strengthen carrier identity out of order, but
-- payment stays at the first unclosed causal discriminator.
------------------------------------------------------------------------

record Same88AcquisitionState : Set where
  constructor same-88-acquisition-state
  field
    Davies2017Acquired : Bool
    Davies2018DeclineAcquired : Bool
    Davies2020DisturbanceCatAcquired : Bool
    Penton2021Acquired : Bool
    Neave2025TrailAcquired : Bool
    herbivoryQidAcquired : Bool
    catQidAcquired : Bool
    rabbitRatQidAcquired : Bool
    outOfOrderEvidenceRetained : Bool

record Same88PaymentState : Set where
  constructor same-88-payment-state
  field
    sourceIdentityPaid : Bool
    attributionPaid : Bool
    surveyNetworkIdentityPaid : Bool
    exactSiteSetPaid : Bool
    exactRowJoinPaid : Bool
    fireToShrubPaid : Bool
    herbivoreToShrubPaid : Bool
    shrubToCatPaid : Bool
    catToTaxonPaid : Bool
    causalMediationPaid : Bool
    firstUnpaidGate : String

snowballAcquisitionDoesNotAdvanceSame88Payment : Same88AcquisitionState → Same88PaymentState → Same88PaymentState
snowballAcquisitionDoesNotAdvanceSame88Payment _ payment = payment

firstUnpaidEmpiricalDiscriminator : String
firstUnpaidEmpiricalDiscriminator = Ledger.firstUnpaidEmpiricalDiscriminator

firstUnpaidMultiDriverDiscriminator : String
firstUnpaidMultiDriverDiscriminator = Mega.firstUnpaidMultiDriverDiscriminator

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

traversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
traversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary
