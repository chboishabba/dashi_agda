module DASHI.Wikimedia.IbrahimSnowballTiwiFireStructureMammalBidiFactorsThroughExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballTiwiShrubPredationMediationDeweyDoiQidExact as Shrub
import DASHI.Wikimedia.IbrahimSnowballTiwiSameExperimentFireBiodiversityCarbonExact as Experiment

------------------------------------------------------------------------
-- TIWI FIRE / STRUCTURE / MAMMAL BIDI SNOWBALL
--
-- Forward direction:
--   manipulated fire frequency -> measured woody structure -> mammal response
-- with structure/predation mediation still consumer-indexed.
--
-- Reverse direction:
--   mammal outcomes constrain which fire summaries are adequate.  In
-- particular a scalar pyrodiversity summary cannot recover the underlying
-- mixture of fire treatments or its mammal consequence.
--
-- Source attribution is exact: external studies own their empirical claims;
-- DASHI owns only formal crosswalks, finite no-go witnesses and cross-source
-- inference.  QID/DOI/Dewey are navigation/provenance coordinates, not proof.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- QID snowball.  Reuse paid identities and keep uncertain identities open.
------------------------------------------------------------------------

fireEcologyQid : Identity.ExternalIdentityDemand
fireEcologyQid = Identity.mkOptionalIdentityDemand
  "Tiwi fire-structure-mammal BIDI continuation" "external ecological concept identity"
  "fire ecology" Identity.wikidataQid
  (Identity.unresolved "No safely verified exact fire-ecology concept QID promoted in this tranche; article/category items are not concept substitutes")

groundCoverQid : Identity.ExternalIdentityDemand
groundCoverQid = Identity.mkOptionalIdentityDemand
  "Tiwi fire-structure-mammal BIDI continuation" "external habitat-structure identity"
  "ground cover / ground-layer vegetation" Identity.wikidataQid
  (Identity.unresolved "No safely verified exact ground-cover ecological concept QID promoted in this tranche")

brushTailedRabbitRatQid : Identity.ExternalIdentityDemand
brushTailedRabbitRatQid = Shrub.brushTailedRabbitRatQid

------------------------------------------------------------------------
-- Ibrahim/Dewey/DOI coordinates.
------------------------------------------------------------------------

fireMixtureCoordinate : Traversal.DashiKnowledgeCoordinate
fireMixtureCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiFireStructureMammalBidiFactorsThroughExact.agda"
  "Tiwi experimental fire-mixture / pyrodiversity consumer"
  "577.4 — savanna ecology; classification coordinate only"
  "fire ecology QID unresolved"
  "DOI 10.1111/1365-2664.13170"

mechanismDonorCoordinate : Traversal.DashiKnowledgeCoordinate
mechanismDonorCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiFireStructureMammalBidiFactorsThroughExact.agda"
  "ground-cover loss / post-fire predation mechanism donor"
  "577.4 — tropical-savanna ecology context; not Tiwi same-object identity"
  "ground-cover QID unresolved; Q146 identifies cat only"
  "DOI 10.1071/WR15011; DOI 10.1038/srep22559"

mammalOutcomeCoordinate : Traversal.DashiKnowledgeCoordinate
mammalOutcomeCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiFireStructureMammalBidiFactorsThroughExact.agda"
  "species-specific Tiwi mammal abundance / extinction-risk consumer"
  "599 — Mammalia; taxon coordinates remain separate"
  "Q303877 and prior paid Tiwi mammal QIDs"
  "DOI 10.1111/1365-2664.13170"

fireMixtureSupportsMammalOutcome : Traversal.DashiFirstLinkEdge
fireMixtureSupportsMammalOutcome = Traversal.dashi-first-link-edge
  fireMixtureCoordinate mammalOutcomeCoordinate Traversal.supportedBy
  Traversal.canonicalDashiFirstLinkPolicy
  "Davies et al. experimentally estimate species-specific abundance under annual, triennial and long-unburnt treatments and show outcome depends on treatment mixture, not pyrodiversity scalar alone"
  true

mechanismDonorCrossPollinatesTiwi : Traversal.DashiFirstLinkEdge
mechanismDonorCrossPollinatesTiwi = Traversal.dashi-first-link-edge
  mechanismDonorCoordinate mammalOutcomeCoordinate Traversal.crossPollinatesWith
  Traversal.canonicalDashiFirstLinkPolicy
  "Leahy/McGregor provide northern-savanna mechanism donors for cover loss and predator response; they do not pay Tiwi same-population mediation"
  true

------------------------------------------------------------------------
-- Exact source roles.
------------------------------------------------------------------------

data BidiSourceRole : Set where
  tiwiExperimentalFireMammalResponse
  tiwiExperimentalWoodyStructureResponse
  controlledGroundCoverPredationMechanism
  predatorFireScarMovementMechanism
  longFireExclusionVegetationFaunaComparison : BidiSourceRole

record BidiPrimarySource : Set where
  constructor bidi-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    role : BidiSourceRole
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open BidiPrimarySource public

daviesEtAl2018 : BidiPrimarySource
daviesEtAl2018 = bidi-primary-source
  "Hugh F. Davies; Michael A. McCarthy; Willie Rioli; José Puruntatameri; Willie Roberts; Colin Kerinaiua; Vivian Kerinauia; Kim Brooks Womatakimi; Alan N. Andersen; Brett P. Murphy"
  "An experimental test of whether pyrodiversity promotes mammal diversity in a northern Australian savanna"
  "Journal of Applied Ecology 55(5):2124-2134"
  2018
  "DOI 10.1111/1365-2664.13170; Dryad 10.5061/dryad.4gm2r5m"
  tiwiExperimentalFireMammalResponse
  "Primary Tiwi experiment using all 18 fire plots; fire treatment predicts abundance for most analysed mammal groups, species prefer different treatments, and equal pyrodiversity can conceal different fire mixtures and mammal outcomes."
  "Does not prove shrub or predation mediation, does not imply maximal pyrodiversity is optimal, and does not transfer one species' response sign to another."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner

freemanEtAl2018 : BidiPrimarySource
freemanEtAl2018 = bidi-primary-source
  "Michelle E. Freeman; Brett P. Murphy; Anna E. Richards; Peter A. Vesk; Garry D. Cook"
  "Facultative and Obligate Trees in a Mesic Savanna: Fire Effects on Savanna Structure Imply Contrasting Strategies of Eco-Taxonomic Groups"
  "Frontiers in Plant Science 9:644"
  2018
  "DOI 10.3389/fpls.2018.00644"
  tiwiExperimentalWoodyStructureResponse
  "Primary Tiwi Carbon Study vegetation follow-up: six years of annual/triennial/fire-exclusion treatments alter woody size-class structure, with eco-taxonomic groups responding differently."
  "Shrubs, palms and cycads were excluded from the census; tree/sapling structure therefore does not pay the shrub-density mediation gate."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner

leahyEtAl2015 : BidiPrimarySource
leahyEtAl2015 = bidi-primary-source
  "Lily Leahy; Sarah M. Legge; Katherine Tuft; Hugh W. McGregor; Leon A. Barmuta; Menna E. Jones; Christopher N. Johnson"
  "Amplified predation after fire suppresses rodent populations in Australia's tropical savannas"
  "Wildlife Research 42(8):705-716"
  2015
  "DOI 10.1071/WR15011"
  controlledGroundCoverPredationMechanism
  "Primary controlled northern-savanna experiment comparing high-intensity fire, low-intensity patchy fire and unburnt control for Rattus tunneyi and Pseudomys nanus; high-intensity fire removed ground vegetation, post-fire predation mortality increased, and radio-tracking supported predation rather than direct fire mortality, food loss, reproduction or emigration as the main measured mechanism."
  "This is not Melville/Tiwi, not the same taxa as all Tiwi consumers, and cannot by itself pay Tiwi shrub or predator mediation."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner

mcGregorEtAl2016 : BidiPrimarySource
mcGregorEtAl2016 = bidi-primary-source
  "Hugh W. McGregor; Sarah Legge; Menna E. Jones; Christopher N. Johnson"
  "Extraterritorial hunting expeditions to intense fire scars by feral cats"
  "Scientific Reports 6:22559"
  2016
  "DOI 10.1038/srep22559"
  predatorFireScarMovementMechanism
  "Primary GPS study in the Kimberley showing directed cat movements to recent intense fire scars, with mild burns retaining unburnt ground-cover patches and not eliciting the same observed journeys."
  "Predator movement to fire scars is not direct prey-mortality measurement and is not a Tiwi same-carrier receipt."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner

woinarskiEtAl2004 : BidiPrimarySource
woinarskiEtAl2004 = bidi-primary-source
  "John C. Z. Woinarski; J. Risler; L. Kean"
  "Response of vegetation and vertebrate fauna to 23 years of fire exclusion in a tropical Eucalyptus open forest, Northern Territory, Australia"
  "Austral Ecology 29(2):156-176"
  2004
  "DOI 10.1111/j.1442-9993.2004.01333.x"
  longFireExclusionVegetationFaunaComparison
  "Primary long-duration comparison of a fire-excluded block with an annually burnt adjacent block; reports major tree/shrub composition differences and vertebrate-composition differences under that site history."
  "Opportunistic adjacent-block comparison is not randomized Tiwi evidence and does not establish the Tiwi causal mediation chain."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner

------------------------------------------------------------------------
-- BIDI core: forward evidence plus reverse adequacy constraints.
------------------------------------------------------------------------

data FireMixture : Set where
  mixtureA mixtureB : FireMixture

data PyrodiversitySummary : Set where
  sameIntermediatePyrodiversity : PyrodiversitySummary

data MammalOutcome : Set where
  higherAssemblageOutcome lowerAssemblageOutcome : MammalOutcome

pyrodiversitySummary : FireMixture → PyrodiversitySummary
pyrodiversitySummary mixtureA = sameIntermediatePyrodiversity
pyrodiversitySummary mixtureB = sameIntermediatePyrodiversity

mammalOutcome : FireMixture → MammalOutcome
mammalOutcome mixtureA = higherAssemblageOutcome
mammalOutcome mixtureB = lowerAssemblageOutcome

pyrodiversityCannotRecoverMammalOutcome :
  INF.FactorsThrough pyrodiversitySummary mammalOutcome → ⊥
pyrodiversityCannotRecoverMammalOutcome =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness mixtureA mixtureB refl (λ ()))

record ForwardFireStructureReceipt : Set where
  constructor forward-fire-structure-receipt
  field
    experimentSource : BidiPrimarySource
    vegetationSource : BidiPrimarySource
    sameTiwiExperimentFamily : Bool
    manipulatedFireFrequency : Bool
    woodyStructureMeasured : Bool
    mammalAbundanceMeasured : Bool
    exactSameSamplingUnit : Bool
    shrubDensityMeasuredInVegetationExperiment : Bool
    predationMediationMeasuredInTiwiExperiment : Bool

open ForwardFireStructureReceipt public

canonicalForwardFireStructureReceipt : ForwardFireStructureReceipt
canonicalForwardFireStructureReceipt = forward-fire-structure-receipt
  daviesEtAl2018 freemanEtAl2018
  true true true true false false false

record ReverseMammalConstraintReceipt : Set where
  constructor reverse-mammal-constraint-receipt
  field
    speciesResponsesDiffer : Bool
    samePyrodiversityCanHideDifferentMixtures : Bool
    samePyrodiversityCanHideDifferentOutcomes : Bool
    maximalPyrodiversityUniversallyOptimal : Bool
    mammalOutcomeIdentifiesShrubMechanism : Bool
    mammalOutcomeIdentifiesPredatorMechanism : Bool
    mammalOutcomeIdentifiesCountryAuthority : Bool

open ReverseMammalConstraintReceipt public

canonicalReverseMammalConstraintReceipt : ReverseMammalConstraintReceipt
canonicalReverseMammalConstraintReceipt = reverse-mammal-constraint-receipt
  true true true false false false false

record FireStructureMammalBidiFrontier : Set where
  constructor fire-structure-mammal-bidi-frontier
  field
    forwardTiwiFireToWoodyStructurePaid : Bool
    forwardTiwiFireToSpeciesResponsePaid : Bool
    reversePyrodiversityCompressionRuledOut : Bool
    reverseSpeciesUniformityRuledOut : Bool
    coverPredationMechanismDonorAcquired : Bool
    exactTiwiFireToShrubPaid : Bool
    exactTiwiShrubToPredatorPaid : Bool
    exactTiwiPredatorToTaxonPaid : Bool
    fullTiwiMediationPaid : Bool
    dashiInferenceOwner : Attribution.ClaimOwner
    dashiOwnsOnlyComposition : dashiInferenceOwner ≡ Attribution.dashiInferenceOwner

open FireStructureMammalBidiFrontier public

canonicalFireStructureMammalBidiFrontier : FireStructureMammalBidiFrontier
canonicalFireStructureMammalBidiFrontier = fire-structure-mammal-bidi-frontier
  true true true true true
  false false false false
  Attribution.dashiInferenceOwner refl

------------------------------------------------------------------------
-- Snowball acquisition does not pay the remaining mediation gates.
------------------------------------------------------------------------

record FireStructureMammalBidiAcquisitionState : Set where
  constructor fire-structure-mammal-bidi-acquisition-state
  field
    TiwiExperimentAcquired : Bool
    TiwiVegetationAcquired : Bool
    TiwiMammalAcquired : Bool
    MelvilleShrubPredationAcquired : Bool
    LeahyMechanismDonorAcquired : Bool
    McGregorMovementDonorAcquired : Bool
    WoinarskiLongFireExclusionAcquired : Bool
    qidSearchPerformed : Bool
    unresolvedQidsRetained : Bool
    outOfOrderEvidenceRetained : Bool

open FireStructureMammalBidiAcquisitionState public

record FireStructureMammalBidiPaymentState : Set where
  constructor fire-structure-mammal-bidi-payment-state
  field
    exactSourceAttributionPaid : Bool
    qidIdentityPaid : Bool
    deweyClassificationPaid : Bool
    doiSourceIdentityPaid : Bool
    sameTiwiExperimentFamilyPaid : Bool
    fireToWoodyStructurePaid : Bool
    fireToSpeciesResponsePaid : Bool
    pyrodiversityCompressionNoGoPaid : Bool
    exactFireToShrubPaid : Bool
    exactShrubToPredatorPaid : Bool
    exactPredatorToTaxonPaid : Bool
    sameSiteAndWindowPaid : Bool
    fullMediationPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open FireStructureMammalBidiPaymentState public

snowballAcquisitionDoesNotAdvanceBidiPayment :
  FireStructureMammalBidiAcquisitionState →
  FireStructureMammalBidiPaymentState →
  FireStructureMammalBidiPaymentState
snowballAcquisitionDoesNotAdvanceBidiPayment _ payment = payment

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data PyrodiversityMeansFireComposition : Set where
data MammalOutcomeMeansMechanism : Set where
data WoodyStructureMeansShrubDensity : Set where
data MainlandMechanismMeansTiwiMediation : Set where
data SpeciesResponseMeansAssemblageRule : Set where
data FireEffectMeansCountryAuthority : Set where
data QidCreatesEvidence : Set where
data DOITransfersCausality : Set where
data AcquisitionCreatesPayment : Set where

pyrodiversityDoesNotIdentifyComposition : PyrodiversityMeansFireComposition → ⊥
pyrodiversityDoesNotIdentifyComposition ()

mammalOutcomeDoesNotIdentifyMechanism : MammalOutcomeMeansMechanism → ⊥
mammalOutcomeDoesNotIdentifyMechanism ()

woodyStructureDoesNotEqualShrubDensity : WoodyStructureMeansShrubDensity → ⊥
woodyStructureDoesNotEqualShrubDensity ()

mainlandMechanismDoesNotCreateTiwiMediation : MainlandMechanismMeansTiwiMediation → ⊥
mainlandMechanismDoesNotCreateTiwiMediation ()

speciesResponseDoesNotCreateAssemblageRule : SpeciesResponseMeansAssemblageRule → ⊥
speciesResponseDoesNotCreateAssemblageRule ()

fireEffectDoesNotCreateCountryAuthority : FireEffectMeansCountryAuthority → ⊥
fireEffectDoesNotCreateCountryAuthority ()

qidDoesNotCreateEvidence : QidCreatesEvidence → ⊥
qidDoesNotCreateEvidence ()

doiDoesNotTransferCausality : DOITransfersCausality → ⊥
doiDoesNotTransferCausality ()

acquisitionDoesNotCreatePayment : AcquisitionCreatesPayment → ⊥
acquisitionDoesNotCreatePayment ()

------------------------------------------------------------------------
-- Reuse prior snowballs and attribution boundary.
------------------------------------------------------------------------

priorShrubSnowball :
  Shrub.TiwiShrubPredationAcquisitionState →
  Shrub.TiwiShrubPredationPaymentState →
  Shrub.TiwiShrubPredationPaymentState
priorShrubSnowball = Shrub.snowballAcquisitionDoesNotAdvanceTiwiShrubPredationPayment

priorExperimentSnowball :
  Experiment.TiwiSameExperimentAcquisitionState →
  Experiment.TiwiSameExperimentPaymentState →
  Experiment.TiwiSameExperimentPaymentState
priorExperimentSnowball = Experiment.snowballAcquisitionDoesNotAdvanceTiwiSameExperimentPayment

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

traversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
traversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary
