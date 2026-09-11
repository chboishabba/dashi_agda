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
-- IBRAHIM / DEWEY / DOI / QID MULTI-DRIVER CONTINUATION
--
-- The live Tiwi BIDI residual must not be compressed to "fire causes predator
-- access".  Melville-local evidence now exposes at least two distinct upstream
-- route families:
--
--   fire / vegetation-cover history ----\
--                                      > predator accessibility/activity
--   megaherbivore trail structure -----/
--
-- and the prey response remains a further consumer.  Dewey, QID and DOI are
-- retained as classification / identity / source coordinates only.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- QID snowball.  Exact concept identities only; no article-QID substitution.
------------------------------------------------------------------------

savannaQid : Identity.ExternalIdentityDemand
savannaQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver predator-access continuation" "ecosystem identity"
  "savanna / savannah" Identity.wikidataQid
  (Identity.verified "Q42320" "Wikidata savanna item inspected 2026-09-11; ecosystem identity does not create a local ecological observation")

ecologicalDisturbanceQid : Identity.ExternalIdentityDemand
ecologicalDisturbanceQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver predator-access continuation" "ecological-process identity"
  "ecological disturbance" Identity.wikidataQid
  (Identity.verified "Q966490" "Wikidata ecological-disturbance concept inspected 2026-09-11; concept identity does not establish a disturbance effect")

ecologicalConnectivityQid : Identity.ExternalIdentityDemand
ecologicalConnectivityQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver predator-access continuation" "landscape-ecology identity"
  "ecological / landscape connectivity" Identity.wikidataQid
  (Identity.verified "Q2993449" "Wikidata ecological-connectivity concept inspected 2026-09-11; identity does not establish measured movement")

habitatFragmentationQid : Identity.ExternalIdentityDemand
habitatFragmentationQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver predator-access continuation" "landscape-ecology identity"
  "habitat fragmentation" Identity.wikidataQid
  (Identity.verified "Q913302" "Wikidata habitat-fragmentation concept inspected 2026-09-11")

waterBuffaloQid : Identity.ExternalIdentityDemand
waterBuffaloQid = Ledger.waterBuffaloQid

horseQid : Identity.ExternalIdentityDemand
horseQid = Ledger.horseQid

dingoQid : Identity.ExternalIdentityDemand
dingoQid = Ledger.dingoQid

gameTrailQid : Identity.ExternalIdentityDemand
gameTrailQid = Ledger.gameTrailQid

ecosystemEngineerQid : Identity.ExternalIdentityDemand
ecosystemEngineerQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver predator-access continuation" "ecological-role identity"
  "ecosystem engineer" Identity.wikidataQid
  (Identity.unresolved "No safely verified exact Wikidata concept item promoted; ecological engineering Q3738960 is a human design discipline and is not an ecosystem-engineer organism-role identity")

megaherbivoreQid : Identity.ExternalIdentityDemand
megaherbivoreQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver predator-access continuation" "ecological guild identity"
  "megaherbivore" Identity.wikidataQid
  (Identity.unresolved "No safely verified broad megaherbivore concept item promoted; taxon identities remain separate")

------------------------------------------------------------------------
-- Dewey coordinates.  These are browse/classification coordinates only.
------------------------------------------------------------------------

savannaEcologyCoordinate : Traversal.DashiKnowledgeCoordinate
savannaEcologyCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiMultiDriverPredatorAccessDeweyDoiQidExact.agda"
  "savanna ecology / disturbance / multi-driver habitat structure"
  "577.4 — grassland ecology, including savanna and tropical grassland ecology"
  "Q42320; Q966490; Q2993449; Q913302"
  "DOI 10.1002/ece3.71622; DOI 10.1890/06-1599.1"

predatorCoordinate : Traversal.DashiKnowledgeCoordinate
predatorCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiMultiDriverPredatorAccessDeweyDoiQidExact.agda"
  "terrestrial mammalian predator-access consumer"
  "599.7 — Carnivora; consumer classification only"
  "Q38584; Q146"
  "DOI 10.1002/ece3.71622; DOI 10.1038/srep22559"

smallMammalHabitatCoordinate : Traversal.DashiKnowledgeCoordinate
smallMammalHabitatCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiMultiDriverPredatorAccessDeweyDoiQidExact.agda"
  "Tiwi small-mammal habitat consumer"
  "599 — Mammalia; exact taxon fibres remain separate"
  "Q303877; Q52105"
  "DOI 10.1111/j.1365-2699.2006.01543.x"

multiDriverToPredatorAccess : Traversal.DashiFirstLinkEdge
multiDriverToPredatorAccess = Traversal.dashi-first-link-edge
  savannaEcologyCoordinate predatorCoordinate Traversal.crossPollinatesWith
  Traversal.canonicalDashiFirstLinkPolicy
  "fire/cover and megaherbivore-created linear features are distinct candidate upstream coordinates for predator accessibility; neither route is universal or sufficient by label"
  true

predatorAccessToSmallMammalConsumer : Traversal.DashiFirstLinkEdge
predatorAccessToSmallMammalConsumer = Traversal.dashi-first-link-edge
  predatorCoordinate smallMammalHabitatCoordinate Traversal.informs
  Traversal.canonicalDashiFirstLinkPolicy
  "predator accessibility may constrain mammal-demography hypotheses, but predator detection/movement does not itself pay prey mortality or population response"
  true

------------------------------------------------------------------------
-- Primary sources attached directly to this continuation.
------------------------------------------------------------------------

data MultiDriverSourceRole : Set where
  MelvillePredatorMicrocorridorStudy
  TiwiSmallMammalHabitatStudy
  northernSavannaBuffaloGroundCoverFireHistory : MultiDriverSourceRole

record MultiDriverPrimarySource : Set where
  constructor multi-driver-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    doi : String
    role : MultiDriverSourceRole
    carrier : String
    boundedClaim : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open MultiDriverPrimarySource public

neaveEtAl2025 : MultiDriverPrimarySource
neaveEtAl2025 = multi-driver-primary-source
  "Georgina Neave; Brett P. Murphy; Tiwi Rangers; Hugh F. Davies"
  "Exotic Megaherbivores as Ecosystem Engineers in Australian Savannas: Do They Facilitate Predator Movement?"
  "Ecology and Evolution 15(7):e71622"
  2025
  "10.1002/ece3.71622; Dryad 10.5061/dryad.0zpc86776"
  MelvillePredatorMicrocorridorStudy
  "52 paired Melville Island camera sites comparing megaherbivore game trails with adjacent undisturbed vegetation"
  "Primary Melville evidence that dingoes and feral cats preferentially use megaherbivore trails; Tiwi Rangers are named collective authors."
  "Trail use is not prey mortality; megaherbivore control is not thereby a native-mammal benefit theorem; authorship does not create whole-Country authority."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner

firthEtAl2006 : MultiDriverPrimarySource
firthEtAl2006 = multi-driver-primary-source
  "Ronald S. C. Firth; John C. Z. Woinarski; Kym G. Brennan; Craig Hempel"
  "Environmental relationships of the brush-tailed rabbit-rat, Conilurus penicillatus, and other small mammals on the Tiwi Islands, northern Australia"
  "Journal of Biogeography 33(10):1820-1837"
  2006
  "10.1111/j.1365-2699.2006.01543.x"
  TiwiSmallMammalHabitatStudy
  "Tiwi Islands habitat-association survey/model for brush-tailed rabbit-rat and co-occurring small mammals"
  "Primary Tiwi evidence that Conilurus penicillatus was most likely in tall eucalypt forest away from watercourses; several native mammals were not recorded in plantation habitat."
  "Habitat association is not a fire-treatment effect, predator-mediated causal effect, or present-day population status by itself."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner

pettyEtAl2007 : MultiDriverPrimarySource
pettyEtAl2007 = multi-driver-primary-source
  "Aaron M. Petty; Patricia A. Werner; Caroline E. R. Lehmann; Jan E. Riley; Daniel S. Banfai; Lindsay P. Elliott"
  "Savanna responses to feral buffalo in Kakadu National Park, Australia"
  "Ecological Monographs 77(3):441-463"
  2007
  "10.1890/06-1599.1"
  northernSavannaBuffaloGroundCoverFireHistory
  "Kakadu historical-ecology synthesis of buffalo expansion/removal across savanna, floodplain and rainforest contexts"
  "Primary northern-savanna evidence that buffalo history altered ground-cover abundance/composition and fuel regimes with contingent fire interactions and hysteresis."
  "Kakadu is not Melville; historical ecological cascades do not pay a Tiwi same-site mediation or prove that buffalo control restores a previous state."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner

------------------------------------------------------------------------
-- Multi-driver LES/BIDI carrier.
------------------------------------------------------------------------

data UpstreamDriver : Set where
  fireFrequency
  fireIntensity
  timeSinceFire
  shrubUnderstoreyStructure
  megaherbivoreTrailNetwork
  plantationLandUse
  rainfallLandformContext : UpstreamDriver

data PredatorAccessConsumer : Set where
  catDetection
  dingoDetection
  catDirectedMovement
  preyEncounterOpportunity
  preyMortality : PredatorAccessConsumer

record MultiDriverPredatorAccessState : Set where
  constructor multi-driver-predator-access-state
  field
    fireDriverReference : String
    vegetationStructureReference : String
    megaherbivoreTrailReference : String
    predatorReference : String
    preyTaxonReference : String
    spatialCarrierReference : String
    timeCarrierReference : String
    fireToStructurePaid : Bool
    trailToPredatorDetectionPaid : Bool
    structureToPredatorAccessPaid : Bool
    predatorAccessToMortalityPaid : Bool
    mortalityToPopulationResponsePaid : Bool
    sameSiteTimeCompositionPaid : Bool
    dashiInferenceOwner : Attribution.ClaimOwner
    dashiOwnsInferenceOnly : dashiInferenceOwner ≡ Attribution.dashiInferenceOwner

open MultiDriverPredatorAccessState public

canonicalMultiDriverPredatorAccessState : MultiDriverPredatorAccessState
canonicalMultiDriverPredatorAccessState = multi-driver-predator-access-state
  "Tiwi experimental fire + northern-savanna mechanism donors"
  "Melville shrub/understorey and Tiwi woody-structure observations"
  "Neave et al. 2025 megaherbivore game-trail carrier"
  "feral cat and dingo detections / movements"
  "taxon-specific Tiwi mammal consumers"
  "Melville/Tiwi carrier family; exact joins consumer-specific"
  "mixed historical windows; exact contemporaneous join unpaid"
  true true false false false false
  Attribution.dashiInferenceOwner refl

------------------------------------------------------------------------
-- BIDI reverse constraints: neither fire nor vegetation alone is a sufficient
-- representation for predator accessibility once an independent trail-network
-- coordinate is admitted.
------------------------------------------------------------------------

data SameFireMeansSamePredatorAccess : Set where
data SameVegetationMeansSamePredatorAccess : Set where
data PredatorDetectionMeansPredationMortality : Set where
data MegaherbivoreControlMeansNativeMammalBenefit : Set where
data EcosystemEngineerLabelMeansBeneficialEngineering : Set where
data EcologicalEngineeringQidMeansEcosystemEngineer : Set where
data ArticleDoiMeansConceptIdentity : Set where
data DeweyClassMeansCausalParent : Set where
data PrimarySourcesComposeAutomatically : Set where

data MelvilleMeansSameSite : Set where

sameFireDoesNotFixPredatorAccess : SameFireMeansSamePredatorAccess → ⊥
sameFireDoesNotFixPredatorAccess ()

sameVegetationDoesNotFixPredatorAccess : SameVegetationMeansSamePredatorAccess → ⊥
sameVegetationDoesNotFixPredatorAccess ()

predatorDetectionDoesNotCreateMortality : PredatorDetectionMeansPredationMortality → ⊥
predatorDetectionDoesNotCreateMortality ()

megaherbivoreControlDoesNotCreateNativeBenefit : MegaherbivoreControlMeansNativeMammalBenefit → ⊥
megaherbivoreControlDoesNotCreateNativeBenefit ()

ecosystemEngineerLabelDoesNotMeanBenefit : EcosystemEngineerLabelMeansBeneficialEngineering → ⊥
ecosystemEngineerLabelDoesNotMeanBenefit ()

ecologicalEngineeringIsWrongTypeForEngineerOrganism : EcologicalEngineeringQidMeansEcosystemEngineer → ⊥
ecologicalEngineeringIsWrongTypeForEngineerOrganism ()

doiDoesNotCreateConceptIdentity : ArticleDoiMeansConceptIdentity → ⊥
doiDoesNotCreateConceptIdentity ()

deweyDoesNotCreateCausalParent : DeweyClassMeansCausalParent → ⊥
deweyDoesNotCreateCausalParent ()

primarySourcesDoNotAutoCompose : PrimarySourcesComposeAutomatically → ⊥
primarySourcesDoNotAutoCompose ()

MelvilleLabelDoesNotCreateSameSite : MelvilleMeansSameSite → ⊥
MelvilleLabelDoesNotCreateSameSite ()

------------------------------------------------------------------------
-- Snowball: later evidence may be retained, but payment stays consumer- and
-- carrier-relative.
------------------------------------------------------------------------

record MultiDriverAcquisitionState : Set where
  constructor multi-driver-acquisition-state
  field
    savannaQidAcquired : Bool
    disturbanceQidAcquired : Bool
    connectivityQidAcquired : Bool
    fragmentationQidAcquired : Bool
    buffaloQidAcquired : Bool
    horseQidAcquired : Bool
    dingoQidAcquired : Bool
    gameTrailQidAcquired : Bool
    NeavePrimaryAcquired : Bool
    FirthPrimaryAcquired : Bool
    PettyPrimaryAcquired : Bool
    MelvilleTrailEvidenceAcquired : Bool
    TiwiHabitatEvidenceAcquired : Bool
    buffaloGroundCoverFireDonorAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open MultiDriverAcquisitionState public

record MultiDriverPaymentState : Set where
  constructor multi-driver-payment-state
  field
    identityPaid : Bool
    sourceMetadataPaid : Bool
    sourceRolePaid : Bool
    exactSitePaid : Bool
    exactTimePaid : Bool
    exactDriverPaid : Bool
    exactVegetationStatePaid : Bool
    exactTrailNetworkPaid : Bool
    predatorDetectionPaid : Bool
    preyMortalityPaid : Bool
    taxonDemographyPaid : Bool
    sameSiteTimeCompositionPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open MultiDriverPaymentState public

snowballAcquisitionDoesNotAdvanceMultiDriverPayment :
  MultiDriverAcquisitionState → MultiDriverPaymentState → MultiDriverPaymentState
snowballAcquisitionDoesNotAdvanceMultiDriverPayment _ payment = payment

canonicalMultiDriverAcquisition : MultiDriverAcquisitionState
canonicalMultiDriverAcquisition = multi-driver-acquisition-state
  true true true true true true true false
  true true true true true true true

canonicalMultiDriverPayment : MultiDriverPaymentState
canonicalMultiDriverPayment = multi-driver-payment-state
  true true true false false false false false
  true false false false false false
  "Exact same-site/time decomposition of fire/understorey and megaherbivore-trail contributions to predator access, followed by prey-mortality and taxon-demography payment"

------------------------------------------------------------------------
-- Reuse canonical provenance/traversal boundaries.
------------------------------------------------------------------------

ledgerCoverage : Ledger.TiwiBidiSourceCoverageReceipt
ledgerCoverage = Ledger.canonicalTiwiBidiSourceCoverageReceipt

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

traversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
traversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary
