module DASHI.Wikimedia.IbrahimSnowballTiwiPredationHabitatDeweyDoiQidExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal
import DASHI.Wikimedia.IbrahimSnowballTiwiHabitatConnectivityRangerAuthorshipQidExact as Prior

------------------------------------------------------------------------
-- TIWI / NORTHERN SAVANNA PREDATION-HABITAT DEWEY-DOI-QID SNOWBALL
--
-- Continue the Ibrahim walk through the actual ecological consumers exposed by
-- the Tiwi habitat/connectivity lane.  Dewey is classification/navigation;
-- DOI is source identity/provenance; QID is concept/taxon identity/navigation.
-- None of those coordinates pays habitat effect, predation, mediation,
-- Country authority, causal transport, or recommendation.
------------------------------------------------------------------------

habitatQid : Identity.ExternalIdentityDemand
habitatQid = Identity.mkOptionalIdentityDemand
  "Tiwi predation/habitat Ibrahim continuation" "external ecological concept identity"
  "habitat" Identity.wikidataQid
  (Identity.verified "Q52105" "Wikidata habitat concept inspected 2026-09-11; identity is not a habitat-effect receipt")

ecologicalConnectivityQid : Identity.ExternalIdentityDemand
ecologicalConnectivityQid = Identity.mkOptionalIdentityDemand
  "Tiwi predation/habitat Ibrahim continuation" "external ecological concept identity"
  "ecological connectivity" Identity.wikidataQid
  (Identity.verified "Q2993449" "Wikidata ecological-connectivity concept inspected 2026-09-11")

habitatFragmentationQid : Identity.ExternalIdentityDemand
habitatFragmentationQid = Identity.mkOptionalIdentityDemand
  "Tiwi predation/habitat Ibrahim continuation" "external ecological concept identity"
  "habitat fragmentation" Identity.wikidataQid
  (Identity.verified "Q913302" "Wikidata canonical habitat-fragmentation item inspected 2026-09-11; Q1566913 resolves/redirects to this item")

predationQid : Identity.ExternalIdentityDemand
predationQid = Identity.mkOptionalIdentityDemand
  "Tiwi predation/habitat Ibrahim continuation" "external ecological interaction identity"
  "predation" Identity.wikidataQid
  (Identity.verified "Q170430" "Wikidata predation concept inspected 2026-09-11")

invasiveSpeciesQid : Identity.ExternalIdentityDemand
invasiveSpeciesQid = Identity.mkOptionalIdentityDemand
  "Tiwi predation/habitat Ibrahim continuation" "external ecological concept identity"
  "invasive species" Identity.wikidataQid
  (Identity.verified "Q183368" "Wikidata invasive-species concept inspected 2026-09-11")

catQid : Identity.ExternalIdentityDemand
catQid = Identity.mkOptionalIdentityDemand
  "Tiwi predation/habitat Ibrahim continuation" "external taxon/common-name identity"
  "cat / Felis catus" Identity.wikidataQid
  (Identity.verified "Q146" "Wikidata cat item inspected 2026-09-11; taxon/common-name identity does not establish feral population or local impact")

------------------------------------------------------------------------
-- Dewey / DOI / QID coordinates use the existing Ibrahim traversal carrier.
------------------------------------------------------------------------

savannaHabitatCoordinate : Traversal.DashiKnowledgeCoordinate
savannaHabitatCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiPredationHabitatDeweyDoiQidExact.agda"
  "northern savanna habitat / disturbance consumer"
  "577.4 — grassland ecology; OCLC DDC explicitly includes savanna ecology"
  "Q52105"
  "DOI 10.1371/journal.pone.0109097"

connectivityCoordinate : Traversal.DashiKnowledgeCoordinate
connectivityCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiPredationHabitatDeweyDoiQidExact.agda"
  "ecological connectivity / movement-resistance consumer"
  "577 — ecology; classification coordinate only"
  "Q2993449"
  "DOI 10.1002/ece3.73320"

predationCoordinate : Traversal.DashiKnowledgeCoordinate
predationCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiPredationHabitatDeweyDoiQidExact.agda"
  "predation / predator-access consumer"
  "577.4 — savanna ecological-interaction context; not a semantic parent theorem"
  "Q170430"
  "DOI 10.1111/1365-2664.12323"

mammalCoordinate : Traversal.DashiKnowledgeCoordinate
mammalCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiPredationHabitatDeweyDoiQidExact.agda"
  "native mammal taxon/response consumer"
  "599 — Mammalia; 599.2 covers Marsupialia and Monotremata"
  "Q194272; Q732477; Q1763261; Q303877"
  "DOI 10.1111/1365-2664.13170"

brushTailedPossumCoordinate : Traversal.DashiKnowledgeCoordinate
brushTailedPossumCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiPredationHabitatDeweyDoiQidExact.agda"
  "brush-tailed possum taxon consumer"
  "599.232 — Phalangeridae; OCLC DDC includes brush-tailed possums"
  "Q732477"
  "DOI 10.1002/ece3.73320"

habitatSupportsConnectivity : Traversal.DashiFirstLinkEdge
habitatSupportsConnectivity = Traversal.dashi-first-link-edge
  savannaHabitatCoordinate connectivityCoordinate Traversal.crossPollinatesWith
  Traversal.canonicalDashiFirstLinkPolicy
  "habitat/fire/vegetation variables are candidate resistance surfaces for connectivity; this is not a theorem that habitat alone determines gene flow"
  true

habitatSupportsPredation : Traversal.DashiFirstLinkEdge
habitatSupportsPredation = Traversal.dashi-first-link-edge
  savannaHabitatCoordinate predationCoordinate Traversal.supportedBy
  Traversal.canonicalDashiFirstLinkPolicy
  "primary northern-savanna studies separately test predator habitat use and predator access; disturbance-to-predation mediation remains consumer-indexed"
  true

------------------------------------------------------------------------
-- Primary source carriers.  Keep movement/habitat use separate from mortality.
------------------------------------------------------------------------

data PredationHabitatSourceRole : Set where
  predatorHabitatSelectionStudy
  predatorAccessPopulationExperiment
  predatorOccupancyHabitatSurvey : PredationHabitatSourceRole

record PredationHabitatPrimarySource : Set where
  constructor predation-habitat-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    role : PredationHabitatSourceRole
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open PredationHabitatPrimarySource public

mcGregorEtAl2014 : PredationHabitatPrimarySource
mcGregorEtAl2014 = predation-habitat-primary-source
  "Hugh W. McGregor; Sarah Legge; Menna E. Jones; Christopher N. Johnson"
  "Landscape Management of Fire and Grazing Regimes Alters the Fine-Scale Habitat Utilisation by Feral Cats"
  "PLOS ONE 9(10):e109097"
  2014
  "DOI 10.1371/journal.pone.0109097"
  predatorHabitatSelectionStudy
  "Primary GPS-collar field study of 32 feral cats in landscapes with contrasting fire and grazing; cats selected open/heavily grazed and recently intensely burnt habitat under the study conditions."
  "Habitat selection does not itself measure prey mortality, does not prove a universal fire-cat effect, and is not the same Tiwi carrier as Davies or Carey."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner

frankEtAl2014 : PredationHabitatPrimarySource
frankEtAl2014 = predation-habitat-primary-source
  "Anke S. K. Frank; Chris N. Johnson; Joanne M. Potts; Alaric Fisher; Katherine Tuft; Ian J. Radford; Iain J. Gordon; Mary-Anne Collis; Sarah Legge"
  "Experimental evidence that feral cats cause local extirpation of small mammals in Australia's tropical savannas"
  "Journal of Applied Ecology"
  2014
  "DOI 10.1111/1365-2664.12323"
  predatorAccessPopulationExperiment
  "Primary field experiment with paired predator-access versus predator-proof compartments in tropical savanna; introduced Rattus villosissimus populations persisted without predator access and declined to local extinction in both cat-accessible compartments over the experiment."
  "The enclosure result does not establish fire mediation, does not transfer automatically to Tiwi taxa, and local extirpation is not regional extinction."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner

stoboWilsonEtAl2020 : PredationHabitatPrimarySource
stoboWilsonEtAl2020 = predation-habitat-primary-source
  "Alyson M. Stobo-Wilson et al."
  "Habitat structural complexity explains patterns of feral cat and dingo occurrence in monsoonal Australia"
  "Diversity and Distributions"
  2020
  "DOI 10.1111/ddi.13065"
  predatorOccupancyHabitatSurvey
  "Primary camera-trap survey across 376 sites and approximately 370000 km2 of monsoonal Northern Territory; models predator occurrence against habitat structural complexity and other environmental/disturbance predictors."
  "Observational occupancy association does not itself establish predation mortality or causal habitat mediation."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner

------------------------------------------------------------------------
-- Evidence and payment remain separate.
------------------------------------------------------------------------

record PredationHabitatEvidenceCell : Set where
  constructor predation-habitat-evidence-cell
  field
    source : PredationHabitatPrimarySource
    siteReference : String
    taxonReference : String
    habitatStructureReference : String
    disturbanceReference : String
    predatorUseReference : String
    predationPopulationReference : String
    exactMeasurementWindow : String
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner
    dashiCrosswalkOwner : Attribution.ClaimOwner
    dashiOwnsCrosswalkOnly : dashiCrosswalkOwner ≡ Attribution.dashiFormalisationOwner

open PredationHabitatEvidenceCell public

record PredationHabitatAcquisitionState : Set where
  constructor predation-habitat-acquisition-state
  field
    qidsAcquired : Bool
    deweyCoordinatesAcquired : Bool
    doiSourcesAcquired : Bool
    sourceRolesAcquired : Bool
    habitatEvidenceAcquired : Bool
    fireEvidenceAcquired : Bool
    grazingEvidenceAcquired : Bool
    catUseEvidenceAcquired : Bool
    predatorAccessExperimentAcquired : Bool
    TiwiTaxonEvidenceAcquired : Bool
    CareyConnectivityEvidenceAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open PredationHabitatAcquisitionState public

record PredationHabitatPaymentState : Set where
  constructor predation-habitat-payment-state
  field
    qidIdentityPaid : Bool
    deweyClassificationPaid : Bool
    doiSourceIdentityPaid : Bool
    sourceRoleAttributionPaid : Bool
    exactHabitatPaid : Bool
    exactPredatorPopulationPaid : Bool
    exactPreyTaxonPaid : Bool
    exactSitePaid : Bool
    exactTimePaid : Bool
    predatorHabitatUsePaid : Bool
    predationPopulationEffectPaid : Bool
    fireToHabitatPaid : Bool
    habitatToPredationMediationPaid : Bool
    sameTiwiPopulationPaid : Bool
    sameTiwiMeasurementWindowPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open PredationHabitatPaymentState public

snowballAcquisitionDoesNotAdvancePredationHabitatPayment :
  PredationHabitatAcquisitionState → PredationHabitatPaymentState → PredationHabitatPaymentState
snowballAcquisitionDoesNotAdvancePredationHabitatPayment _ payment = payment

------------------------------------------------------------------------
-- WrongType / no-promotion barriers.
------------------------------------------------------------------------

data DeweyClassMeansSemanticParent : Set where
data QidMeansEcologicalEvidence : Set where
data DOIIdentifiesConcept : Set where
data FeralCatPresenceMeansPredation : Set where
data BurnedHabitatSelectionMeansPredationMortality : Set where
data MainlandCatExperimentMeansTiwiCausality : Set where
data HabitatComplexityAssociationMeansMediation : Set where
data ConnectivityMeansAbundance : Set where
data InvasiveSpeciesLabelMeansLocalImpact : Set where
data CountryAuthorityMeansPredationEffect : Set where
data EcologicalEffectMeansCountryAuthority : Set where
data AcquisitionCreatesPayment : Set where

deweyClassDoesNotCreateSemanticParent : DeweyClassMeansSemanticParent → ⊥
deweyClassDoesNotCreateSemanticParent ()

qidDoesNotCreateEcologicalEvidence : QidMeansEcologicalEvidence → ⊥
qidDoesNotCreateEcologicalEvidence ()

doiDoesNotIdentifyConcept : DOIIdentifiesConcept → ⊥
doiDoesNotIdentifyConcept ()

feralCatPresenceDoesNotEqualPredation : FeralCatPresenceMeansPredation → ⊥
feralCatPresenceDoesNotEqualPredation ()

burnedHabitatSelectionDoesNotEqualPredationMortality : BurnedHabitatSelectionMeansPredationMortality → ⊥
burnedHabitatSelectionDoesNotEqualPredationMortality ()

mainlandCatExperimentDoesNotCreateTiwiCausality : MainlandCatExperimentMeansTiwiCausality → ⊥
mainlandCatExperimentDoesNotCreateTiwiCausality ()

habitatComplexityAssociationDoesNotCreateMediation : HabitatComplexityAssociationMeansMediation → ⊥
habitatComplexityAssociationDoesNotCreateMediation ()

connectivityDoesNotEqualAbundance : ConnectivityMeansAbundance → ⊥
connectivityDoesNotEqualAbundance ()

invasiveSpeciesLabelDoesNotCreateLocalImpact : InvasiveSpeciesLabelMeansLocalImpact → ⊥
invasiveSpeciesLabelDoesNotCreateLocalImpact ()

countryAuthorityDoesNotCreatePredationEffect : CountryAuthorityMeansPredationEffect → ⊥
countryAuthorityDoesNotCreatePredationEffect ()

ecologicalEffectDoesNotCreateCountryAuthority : EcologicalEffectMeansCountryAuthority → ⊥
ecologicalEffectDoesNotCreateCountryAuthority ()

acquisitionDoesNotCreatePayment : AcquisitionCreatesPayment → ⊥
acquisitionDoesNotCreatePayment ()

priorConnectivitySnowball : Prior.TiwiConnectivityAcquisitionState → Prior.TiwiConnectivityPaymentState → Prior.TiwiConnectivityPaymentState
priorConnectivitySnowball = Prior.snowballAcquisitionDoesNotAdvanceTiwiConnectivityPayment

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

traversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
traversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary
