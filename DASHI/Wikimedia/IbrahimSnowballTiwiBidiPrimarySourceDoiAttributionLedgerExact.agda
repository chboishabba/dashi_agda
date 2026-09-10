module DASHI.Wikimedia.IbrahimSnowballTiwiBidiPrimarySourceDoiAttributionLedgerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballTiwiFireStructureMammalBidiFactorsThroughExact as Bidi
import DASHI.Wikimedia.IbrahimSnowballTiwiShrubPredationMediationDeweyDoiQidExact as Shrub
import DASHI.Wikimedia.IbrahimSnowballTiwiSameExperimentFireBiodiversityCarbonExact as Experiment

------------------------------------------------------------------------
-- PRIMARY-SOURCE / DOI / ATTRIBUTION LEDGER FOR THE TIWI BIDI SNOWBALL
--
-- This is a provenance/payment owner, not a new ecological model.  It makes
-- explicit which exact primary source owns each empirical edge currently used
-- by the Tiwi fire/vegetation/predator/mammal BIDI lane.  DOI is source
-- identity; QID is concept/taxon identity; Dewey is classification; none of
-- them imports the empirical result or creates causal authority.
--
-- External authors own external empirical claims.  DASHI owns only the typed
-- crosswalk, no-go theorem, and cross-source composition/inference.
------------------------------------------------------------------------

data EmpiricalEdgeKind : Set where
  experimentDefinition
  fireToWoodyStructure
  fireToMammalResponse
  shrubCatTaxonAssociation
  predatorToRabbitRatDemography
  hollowUnderstoreyMultiTaxonResponse
  fireGroundCoverPredationMechanism
  fireScarPredatorMovement
  longFireExclusionVegetationFauna
  longTermCarbonStock : EmpiricalEdgeKind

data CarrierRelation : Set where
  exactTiwiExperimentFamily
  MelvilleIslandLocal
  northernSavannaMechanismDonor
  northernTerritoryComparisonDonor : CarrierRelation

record PrimaryEdgeSourcePayment : Set where
  constructor primary-edge-source-payment
  field
    edge : EmpiricalEdgeKind
    canonicalSourceValue : String
    authors : String
    title : String
    publication : String
    year : Nat
    doiOrRepositoryIdentifier : String
    carrierRelation : CarrierRelation
    boundedClaim : String
    excludedPromotion : String
    primarySourceAttached : Bool
    primarySourceAttachedIsTrue : primarySourceAttached ≡ true
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner
    dashiRelationshipOwner : Attribution.ClaimOwner
    dashiOwnsOnlyRelationship : dashiRelationshipOwner ≡ Attribution.dashiFormalisationOwner

open PrimaryEdgeSourcePayment public

richardsExperimentPayment : PrimaryEdgeSourcePayment
richardsExperimentPayment = primary-edge-source-payment
  experimentDefinition
  "Experiment.richardsEtAl2012"
  "Anna E. Richards et al."
  "Savanna burning, greenhouse gas emissions and indigenous livelihoods: Introducing the Tiwi Carbon Study"
  "Austral Ecology 37(6):712-723"
  2012
  "DOI 10.1111/j.1442-9993.2012.02395.x"
  exactTiwiExperimentFamily
  "Defines the Tiwi Carbon Study fire-treatment network and baseline carbon/fauna context."
  "Experiment definition does not itself pay later vegetation, mammal, mediation, productivity or universal Indigenous-fire effects."
  true refl Attribution.externalSourceOwner refl Attribution.dashiFormalisationOwner refl

freemanStructurePayment : PrimaryEdgeSourcePayment
freemanStructurePayment = primary-edge-source-payment
  fireToWoodyStructure
  "Bidi.freemanEtAl2018"
  "Michelle E. Freeman; Brett P. Murphy; Anna E. Richards; Peter A. Vesk; Garry D. Cook"
  "Facultative and Obligate Trees in a Mesic Savanna: Fire Effects on Savanna Structure Imply Contrasting Strategies of Eco-Taxonomic Groups"
  "Frontiers in Plant Science 9:644"
  2018
  "DOI 10.3389/fpls.2018.00644"
  exactTiwiExperimentFamily
  "Primary Tiwi experimental evidence that manipulated fire frequency alters woody size-class structure."
  "Shrubs/palms/cycads were excluded; this does not pay the exact fire-to-shrub-density mediation gate."
  true refl Attribution.externalSourceOwner refl Attribution.dashiFormalisationOwner refl

daviesExperimentPayment : PrimaryEdgeSourcePayment
daviesExperimentPayment = primary-edge-source-payment
  fireToMammalResponse
  "Bidi.daviesEtAl2018"
  "Hugh F. Davies; Michael A. McCarthy; Willie Rioli; José Puruntatameri; Willie Roberts; Colin Kerinaiua; Vivian Kerinauia; Kim Brooks Womatakimi; Alan N. Andersen; Brett P. Murphy"
  "An experimental test of whether pyrodiversity promotes mammal diversity in a northern Australian savanna"
  "Journal of Applied Ecology 55(5):2124-2134"
  2018
  "DOI 10.1111/1365-2664.13170; Dryad DOI 10.5061/dryad.4gm2r5m"
  exactTiwiExperimentFamily
  "Primary Tiwi experimental evidence for species-specific mammal responses to annual, triennial and long-unburnt treatments; also supplies the consumer-side counterexample to scalar pyrodiversity sufficiency."
  "Does not pay shrub mediation, predator mediation, or a universal pyrodiversity-benefit rule."
  true refl Attribution.externalSourceOwner refl Attribution.dashiFormalisationOwner refl

daviesPredationPayment : PrimaryEdgeSourcePayment
daviesPredationPayment = primary-edge-source-payment
  predatorToRabbitRatDemography
  "Shrub.daviesEtAl2017"
  "Hugh F. Davies; Michael A. McCarthy; Ronald S. C. Firth; John C. Z. Woinarski; Graeme R. Gillespie; Alan N. Andersen; Hayley M. Geyle; Emily Nicholson; Brett P. Murphy"
  "Top-down control of species distributions: feral cats driving the regional extinction of a threatened rodent in northern Australia"
  "Diversity and Distributions 23(3):272-283"
  2017
  "DOI 10.1111/ddi.12522"
  MelvilleIslandLocal
  "Primary Melville Island occupancy/dynamic evidence linking brush-tailed rabbit-rat persistence/extinction risk with feral-cat detection and habitat covariates over the study history."
  "Does not by itself identify the complete fire-to-shrub-to-cat causal mediation chain."
  true refl Attribution.externalSourceOwner refl Attribution.dashiFormalisationOwner refl

pentonUnderstoreyPayment : PrimaryEdgeSourcePayment
pentonUnderstoreyPayment = primary-edge-source-payment
  hollowUnderstoreyMultiTaxonResponse
  "Shrub.pentonEtAl2021"
  "Cara E. Penton; Hugh F. Davies; Ian J. Radford; Leigh-Ann Woolley; Tiwi Land Rangers; Brett P. Murphy"
  "A Hollow Argument: Understory Vegetation and Disturbance Determine Abundance of Hollow-Dependent Mammals in an Australian Tropical Savanna"
  "Frontiers in Ecology and Evolution 9:739550"
  2021
  "DOI 10.3389/fevo.2021.739550"
  MelvilleIslandLocal
  "Primary Melville Island multi-taxon evidence separating hollow availability, shrub density, fire/disturbance and cat activity; shrub-density associations are species-specific."
  "Tiwi Land Rangers named collective authorship is retained exactly; study results do not create whole-Country authority and associations do not become complete mediation."
  true refl Attribution.externalSourceOwner refl Attribution.dashiFormalisationOwner refl

leahyMechanismPayment : PrimaryEdgeSourcePayment
leahyMechanismPayment = primary-edge-source-payment
  fireGroundCoverPredationMechanism
  "Bidi.leahyEtAl2015"
  "Lily Leahy; Sarah M. Legge; Katherine Tuft; Hugh W. McGregor; Leon A. Barmuta; Menna E. Jones; Christopher N. Johnson"
  "Amplified predation after fire suppresses rodent populations in Australia's tropical savannas"
  "Wildlife Research 42(8):705-716"
  2015
  "DOI 10.1071/WR15011"
  northernSavannaMechanismDonor
  "Controlled northern-savanna mechanism donor testing direct fire mortality, food loss, reproduction, emigration and increased post-fire predation after ground-cover removal."
  "Not a Tiwi same-population or same-site receipt; transport remains unpaid."
  true refl Attribution.externalSourceOwner refl Attribution.dashiFormalisationOwner refl

mcGregorMovementPayment : PrimaryEdgeSourcePayment
mcGregorMovementPayment = primary-edge-source-payment
  fireScarPredatorMovement
  "Bidi.mcGregorEtAl2016"
  "Hugh W. McGregor; Sarah Legge; Menna E. Jones; Christopher N. Johnson"
  "Extraterritorial hunting expeditions to intense fire scars by feral cats"
  "Scientific Reports 6:22559"
  2016
  "DOI 10.1038/srep22559"
  northernSavannaMechanismDonor
  "Primary GPS evidence that feral cats undertake directed movements to recent intense fire scars."
  "Predator movement does not equal prey mortality and does not pay Tiwi same-carrier mediation."
  true refl Attribution.externalSourceOwner refl Attribution.dashiFormalisationOwner refl

woinarskiComparisonPayment : PrimaryEdgeSourcePayment
woinarskiComparisonPayment = primary-edge-source-payment
  longFireExclusionVegetationFauna
  "Bidi.woinarskiEtAl2004"
  "John C. Z. Woinarski; J. Risler; L. Kean"
  "Response of vegetation and vertebrate fauna to 23 years of fire exclusion in a tropical Eucalyptus open forest, Northern Territory, Australia"
  "Austral Ecology 29(2):156-176"
  2004
  "DOI 10.1111/j.1442-9993.2004.01333.x"
  northernTerritoryComparisonDonor
  "Long-duration adjacent-block comparison recording major vegetation/fuel and vertebrate-composition differences under fire exclusion versus annual burning."
  "Opportunistic comparison is not randomized Tiwi evidence and does not replace an exact Tiwi mediation receipt."
  true refl Attribution.externalSourceOwner refl Attribution.dashiFormalisationOwner refl

ngCarbonPayment : PrimaryEdgeSourcePayment
ngCarbonPayment = primary-edge-source-payment
  longTermCarbonStock
  "Experiment.ngEtAl2026"
  "Ee Ling Ng; Jacqueline R. England; Keryn I. Paul; Melissa Piper; Anna E. Richards; Robyn A. Cowley; Rodd M. Dyer; Jon Schatz; David I. Forrester"
  "Effects of fire management on biomass and debris carbon stocks in Australia's northern savannas: results from long-term trials"
  "International Journal of Wildland Fire 35:WF26061"
  2026
  "DOI 10.1071/WF26061"
  exactTiwiExperimentFamily
  "Long-term fire-trial carbon-stock evidence including the Tiwi trial sites and multiple biomass/debris carbon pools."
  "Carbon stocks do not equal GPP, NEP, NBP, same-time fauna measurements, or universal carbon benefit."
  true refl Attribution.externalSourceOwner refl Attribution.dashiFormalisationOwner refl

------------------------------------------------------------------------
-- Snowball completeness is consumer-relative.  Every currently *paid external
-- empirical edge* above has an explicit primary source/identifier.  The
-- unpaid cross-source mediation remains owned by DASHI inference and cannot be
-- converted into an external-source claim merely because all neighbouring
-- sources are primary.
------------------------------------------------------------------------

record TiwiBidiSourceCoverageReceipt : Set where
  constructor tiwi-bidi-source-coverage-receipt
  field
    experimentDefinitionHasPrimarySource : Bool
    fireToWoodyHasPrimarySource : Bool
    fireToMammalHasPrimarySource : Bool
    MelvillePredationHasPrimarySource : Bool
    MelvilleUnderstoreyHasPrimarySource : Bool
    groundCoverPredationDonorHasPrimarySource : Bool
    catMovementDonorHasPrimarySource : Bool
    longFireComparisonHasPrimarySource : Bool
    longTermCarbonHasPrimarySource : Bool
    everyPaidExternalEmpiricalEdgeHasPrimarySource : Bool
    completeTiwiMediationHasPrimarySource : Bool
    completeTiwiMediationPaid : Bool
    sourceCompletenessDoesNotCreateMediation : Bool

open TiwiBidiSourceCoverageReceipt public

canonicalTiwiBidiSourceCoverageReceipt : TiwiBidiSourceCoverageReceipt
canonicalTiwiBidiSourceCoverageReceipt = tiwi-bidi-source-coverage-receipt
  true true true true true true true true true
  true false false true

------------------------------------------------------------------------
-- QID/Dewey/source identity remain separate payment axes.
------------------------------------------------------------------------

record TiwiBidiIdentityProvenanceSnowball : Set where
  constructor tiwi-bidi-identity-provenance-snowball
  field
    resolvedTaxonQidsRetained : Bool
    unresolvedFireEcologyQidRetained : Bool
    unresolvedGroundCoverQidRetained : Bool
    DeweyCoordinatesRetained : Bool
    DOIIdentifiersRetained : Bool
    authorTitleVenueYearRetained : Bool
    sourceRolesRetained : Bool
    claimOwnersRetained : Bool
    QidMayCreateEmpiricalEdge : Bool
    DOIArrayMayCreateCausality : Bool
    DeweyMayCreateSemanticParent : Bool
    bibliographyCompletenessMayPayMediation : Bool

open TiwiBidiIdentityProvenanceSnowball public

canonicalTiwiBidiIdentityProvenanceSnowball : TiwiBidiIdentityProvenanceSnowball
canonicalTiwiBidiIdentityProvenanceSnowball = tiwi-bidi-identity-provenance-snowball
  true true true true true true true true
  false false false false

data QidCreatesEmpiricalEdge : Set where
data DOICompletenessCreatesCausality : Set where
data PrimarySourcesAroundPathCreateMediation : Set where
data CitationCreatesCountryAuthority : Set where

qidDoesNotCreateEmpiricalEdge : QidCreatesEmpiricalEdge → ⊥
qidDoesNotCreateEmpiricalEdge ()

doiCompletenessDoesNotCreateCausality : DOICompletenessCreatesCausality → ⊥
doiCompletenessDoesNotCreateCausality ()

primarySourcesAroundPathDoNotCreateMediation : PrimarySourcesAroundPathCreateMediation → ⊥
primarySourcesAroundPathDoNotCreateMediation ()

citationDoesNotCreateCountryAuthority : CitationCreatesCountryAuthority → ⊥
citationDoesNotCreateCountryAuthority ()

------------------------------------------------------------------------
-- Canonical first unpaid source-bearing discriminator.
------------------------------------------------------------------------

firstUnpaidEmpiricalDiscriminator : String
firstUnpaidEmpiricalDiscriminator =
  "Exact Tiwi/Melville fire-treatment -> measured shrub/understorey-density source on a carrier joinable to the Davies/Penton fauna-predator observations"

firstUnpaidCompositionDiscriminator : String
firstUnpaidCompositionDiscriminator =
  "Same-site/time causal weld from fire treatment through understorey structure and predator exposure to taxon-specific demographic response"

bidiPaymentBoundary :
  Bidi.FireStructureMammalBidiAcquisitionState →
  Bidi.FireStructureMammalBidiPaymentState →
  Bidi.FireStructureMammalBidiPaymentState
bidiPaymentBoundary = Bidi.snowballAcquisitionDoesNotAdvanceBidiPayment

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

traversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
traversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary
