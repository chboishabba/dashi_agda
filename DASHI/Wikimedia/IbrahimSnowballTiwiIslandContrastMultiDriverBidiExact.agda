module DASHI.Wikimedia.IbrahimSnowballTiwiIslandContrastMultiDriverBidiExact where

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
import DASHI.Wikimedia.IbrahimSnowballTiwiMegaherbivorePredatorAccessDeweyDoiQidExact as Mega

------------------------------------------------------------------------
-- TIWI ISLAND-CONTRAST MULTI-DRIVER BIDI
--
-- Bathurst and Melville provide a useful natural contrast, not a randomized
-- experiment.  Both are Tiwi Islands, but they differ in feral-herbivore
-- presence, cat density, rainfall gradients and disturbance histories.  The
-- contrast is used to prove representation requirements and nominate causal
-- searches; it is not allowed to manufacture a unique causal explanation.
------------------------------------------------------------------------

bathurstIslandQid : Identity.ExternalIdentityDemand
bathurstIslandQid = Identity.mkOptionalIdentityDemand
  "Tiwi island-contrast multi-driver BIDI" "place identity"
  "Bathurst Island, Northern Territory, Australia" Identity.wikidataQid
  (Identity.verified "Q810814" "Wikidata place identity verified 2026-09-11; place identity does not create ecological equivalence or causal control")

melvilleIslandQid : Identity.ExternalIdentityDemand
melvilleIslandQid = Identity.mkOptionalIdentityDemand
  "Tiwi island-contrast multi-driver BIDI" "place identity"
  "Melville Island / Yermalner, Northern Territory, Australia" Identity.wikidataQid
  (Identity.verified "Q504763" "Wikidata place identity verified 2026-09-11; distinct from Canadian Melville Island Q134116")

tiwiIslandsQid : Identity.ExternalIdentityDemand
tiwiIslandsQid = Identity.mkOptionalIdentityDemand
  "Tiwi island-contrast multi-driver BIDI" "place-group identity"
  "Tiwi Islands" Identity.wikidataQid
  (Identity.verified "Q1323908" "Wikidata place-group identity verified 2026-09-11; has Bathurst and Melville as parts")

islandContrastCoordinate : Traversal.DashiKnowledgeCoordinate
islandContrastCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiIslandContrastMultiDriverBidiExact.agda"
  "Bathurst-Melville natural contrast in savanna predator/disturbance ecology"
  "577.4 — savanna ecology; natural-contrast classification only"
  "Q810814; Q504763; Q1323908; Q146; Q42710; Q10758650"
  "DOI 10.1071/PC20088; DOI 10.1071/WR24039; DOI 10.1002/ece3.73320"

record IslandContrastPrimarySource : Set where
  constructor island-contrast-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    boundedClaim : String
    excludedPromotion : String
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner

open IslandContrastPrimarySource public

daviesEtAl2022 : IslandContrastPrimarySource
daviesEtAl2022 = island-contrast-primary-source
  "Hugh F. Davies; Tiwi Land Rangers; Matthew W. Rees; Danielle Stokeld; Anna C. Miller; Graeme R. Gillespie; Brett P. Murphy"
  "Variation in feral cat density between two large adjacent islands in Australia's monsoon tropics"
  "Pacific Conservation Biology 28(1):18-24"
  2022
  "DOI 10.1071/PC20088"
  "Primary four-grid camera study across Bathurst and Melville examining cat density under combinations of fire frequency and feral-herbivore presence. Melville cat density was estimated at 0.15 cats/km2; no cats were detected in the Bathurst grids. Tiwi Land Rangers are named collective authors."
  "The island contrast is not randomized; absence of herbivores on Bathurst may contribute but does not identify a unique herbivore->cat causal effect, and management implications are not outcome proofs."
  Attribution.externalSourceOwner refl

neaveEtAl2024 : IslandContrastPrimarySource
neaveEtAl2024 = island-contrast-primary-source
  "Georgina Neave et al.; Tiwi Rangers"
  "The intact and the imperilled: contrasting mammal population trajectories between two large adjacent islands"
  "Wildlife Research 51:WR24039"
  2024
  "DOI 10.1071/WR24039"
  "Primary Bathurst-Melville mammal comparison: Melville carries water buffalo and horses while Bathurst does not; cat density is much higher on Melville, and mammal trajectories differ between the two islands."
  "Different trajectories do not identify one causal driver; island, rainfall, fire, herbivores, cats and other histories remain separate coordinates."
  Attribution.externalSourceOwner refl

careyEtAl2026 : IslandContrastPrimarySource
careyEtAl2026 = island-contrast-primary-source
  "Alexander R. Carey; Teigan Cremona; Georgina Neave; Hugh F. Davies; Brett P. Murphy; Geoffrey J. Cary; Tiwi Rangers; Sam C. Banks"
  "The Contrasting Role of Fire in Shaping Landscape Genetic Patterns of Small Mammals Across Two Islands"
  "Ecology and Evolution 16(4):e73320"
  2026
  "DOI 10.1002/ece3.73320"
  "Primary landscape-genetic study across Bathurst and Melville; disturbance and connectivity effects are taxon-, island- and scale-specific, with Melville carrying additional cat/herbivore pressure. Tiwi Rangers are named collective authors."
  "Genetic connectivity is not abundance, and cross-island difference does not create a unique fire/herbivore/predator causal explanation."
  Attribution.externalSourceOwner refl

------------------------------------------------------------------------
-- Contrast carrier: similarities nominate controls, differences remain typed.
------------------------------------------------------------------------

data Island : Set where
  Bathurst
  Melville : Island

data ContrastCoordinate : Set where
  islandIdentity
  rainfallRegime
  fireFrequency
  fireSeverity
  feralHerbivorePresence
  feralHerbivoreActivity
  catDensity
  dingoPresence
  understoreyState
  mammalTrajectory
  geneticConnectivity : ContrastCoordinate

record IslandContrastBidiFrontier : Set where
  constructor island-contrast-bidi-frontier
  field
    sameArchipelagoPaid : Bool
    BathurstPlaceQidPaid : Bool
    MelvillePlaceQidPaid : Bool
    catDensityContrastPaid : Bool
    herbivorePresenceContrastPaid : Bool
    mammalTrajectoryContrastPaid : Bool
    geneticContrastEvidencePaid : Bool
    rainfallDifferenceRetained : Bool
    fireDifferenceRetained : Bool
    sameEcologicalBaselinePaid : Bool
    herbivoreToCatCausalEffectPaid : Bool
    fireToCatCausalEffectPaid : Bool
    understoreyMediationPaid : Bool
    uniqueDriverAttributionPaid : Bool
    managementBenefitPaid : Bool

open IslandContrastBidiFrontier public

canonicalIslandContrastBidiFrontier : IslandContrastBidiFrontier
canonicalIslandContrastBidiFrontier = island-contrast-bidi-frontier
  true true true true true true true true true
  false false false false false false

------------------------------------------------------------------------
-- BIDI no-go: the natural contrast proves we need a multi-coordinate carrier,
-- not that one differing coordinate is causal.
------------------------------------------------------------------------

data SameArchipelagoMeansMatchedControl : Set where
data NoHerbivoresAndFewCatsMeansHerbivoresCauseCats : Set where
data DifferentMammalTrajectoryMeansCatCausality : Set where
data EqualFireFrequencyMeansEqualFireRegime : Set where
data PlaceQidCreatesEcologicalEquivalence : Set where
data NaturalContrastCreatesInterventionEffect : Set where
data BetterOutcomeCreatesManagementRecommendation : Set where

sameArchipelagoDoesNotMeanMatchedControl : SameArchipelagoMeansMatchedControl → ⊥
sameArchipelagoDoesNotMeanMatchedControl ()

coOccurrenceContrastDoesNotProveHerbivoreCatCausality : NoHerbivoresAndFewCatsMeansHerbivoresCauseCats → ⊥
coOccurrenceContrastDoesNotProveHerbivoreCatCausality ()

differentTrajectoryDoesNotProveCatCausality : DifferentMammalTrajectoryMeansCatCausality → ⊥
differentTrajectoryDoesNotProveCatCausality ()

equalFireFrequencyDoesNotMeanEqualFireRegime : EqualFireFrequencyMeansEqualFireRegime → ⊥
equalFireFrequencyDoesNotMeanEqualFireRegime ()

placeQidDoesNotCreateEcologicalEquivalence : PlaceQidCreatesEcologicalEquivalence → ⊥
placeQidDoesNotCreateEcologicalEquivalence ()

naturalContrastDoesNotCreateInterventionEffect : NaturalContrastCreatesInterventionEffect → ⊥
naturalContrastDoesNotCreateInterventionEffect ()

betterOutcomeDoesNotCreateManagementRecommendation : BetterOutcomeCreatesManagementRecommendation → ⊥
betterOutcomeDoesNotCreateManagementRecommendation ()

------------------------------------------------------------------------
-- Snowball/payment: natural-contrast evidence is append-only and useful for
-- reverse proof search, but cannot skip the same-carrier causal gates.
------------------------------------------------------------------------

record IslandContrastAcquisitionState : Set where
  constructor island-contrast-acquisition-state
  field
    Davies2022Acquired : Bool
    Neave2024Acquired : Bool
    Carey2026Acquired : Bool
    BathurstQidAcquired : Bool
    MelvilleQidAcquired : Bool
    TiwiIslandsQidAcquired : Bool
    catDensityContrastAcquired : Bool
    mammalTrajectoryContrastAcquired : Bool
    geneticContrastAcquired : Bool
    outOfOrderEvidenceRetained : Bool

record IslandContrastPaymentState : Set where
  constructor island-contrast-payment-state
  field
    sourceIdentityPaid : Bool
    attributionPaid : Bool
    placeIdentityPaid : Bool
    contrastCoordinatesPaid : Bool
    matchedControlPaid : Bool
    herbivoreToStructurePaid : Bool
    fireToStructurePaid : Bool
    structureToCatPaid : Bool
    catToTaxonPaid : Bool
    uniqueCausalAttributionPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGate : String

snowballAcquisitionDoesNotAdvanceIslandContrastPayment :
  IslandContrastAcquisitionState → IslandContrastPaymentState → IslandContrastPaymentState
snowballAcquisitionDoesNotAdvanceIslandContrastPayment _ payment = payment

firstUnpaidSame88Gate : String
firstUnpaidSame88Gate = Same88.firstUnpaidMultiDriverDiscriminator

firstUnpaidIslandContrastGate : String
firstUnpaidIslandContrastGate =
  "Same-carrier measurement of herbivore pressure, understorey structure and cat activity/density sufficient to separate herbivore-mediated predator access from island/rainfall/fire history"

megaherbivoreBoundary : Mega.MultiDriverPredatorAccessFrontier
megaherbivoreBoundary = Mega.canonicalMultiDriverPredatorAccessFrontier

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

traversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
traversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary
