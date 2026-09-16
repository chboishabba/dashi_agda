module DASHI.Law.SensibLawWoogarooLocalKoalaPopulationNexusSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Canonical
import DASHI.Law.SensibLawWoogarooIbrahimPopulationSourceExtensionExact as Population
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom
import DASHI.Law.SensibLawWoogarooPopulationConnectivityAcquisitionExact as Acquisition

------------------------------------------------------------------------
-- LOCAL KOALA POPULATION / CONNECTIVITY NEXUS SNOWBALL
--
-- Highest-alpha extension of the Ibrahim/Dewey/DOI/QID graph.  The purpose is
-- to move from generic SEQ literature toward independent local institutional
-- evidence about Woogaroo/Opossum/Springfield, without pretending that a
-- planning/catchment statement identifies a biological population boundary.
------------------------------------------------------------------------

data SourceGranularity : Set where
  exactProject : SourceGranularity
  localLandscape : SourceGranularity
  regionalSEQ : SourceGranularity
  generalMethod : SourceGranularity

data EvidenceIndependence : Set where
  independentInstitutional : EvidenceIndependence
  independentEmpiricalResearch : EvidenceIndependence
  sameProjectLineage : EvidenceIndependence
  synthesisOrReview : EvidenceIndependence

koalaQid : Id.ItemId
koalaQid = Id.itemId "Q36101"

ecologicalConnectivityQid : Id.ItemId
ecologicalConnectivityQid = Id.itemId "Q2993449"

habitatFragmentationQid : Id.ItemId
habitatFragmentationQid = Id.itemId "Q913302"

landscapeEcologyQid : Id.ItemId
landscapeEcologyQid = Id.itemId "Q738011"

conservationBiologyQid : Id.ItemId
conservationBiologyQid = Id.itemId "Q641498"

springfieldQid : Id.ItemId
springfieldQid = Id.itemId "Q1838932"

cityOfIpswichQid : Id.ItemId
cityOfIpswichQid = Id.itemId "Q1631867"

koalaDewey : String
koalaDewey = "599.25"

conservationBiologyDewey : String
conservationBiologyDewey = "333.9516"

ecologyDewey : String
ecologyDewey = "577.000"

------------------------------------------------------------------------
-- Primary local government sources.
------------------------------------------------------------------------

ipswichWoogarooCatchment : Source.AttributedSource
ipswichWoogarooCatchment = Source.mkNoDOISource
  "Ipswich City Council"
  "Brisbane River Catchment — Woogaroo Creek (including Mountain and Opossum creeks)"
  "Ipswich City Council waterway/catchment information"
  "2026"
  "https://www.ipswich.qld.gov.au/About-Council/Initiatives/Environment/Waterways/Catchments-and-Plans/Brisbane-River-Catchment"
  Source.governmentSource
  "Primary local-government landscape source. It states that the Woogaroo Creek sub-catchment, including Opossum Creek, is an important area for securing urban koala populations and part of the Flinders-Karawatha regional corridor. Used as independent local institutional context, not as a biological population boundary or Springview impact finding."
  Source.publicAttribution

ipswichKoalaPlan : Source.AttributedSource
ipswichKoalaPlan = Source.mkNoDOISource
  "Ipswich City Council"
  "Koala Conservation Plan — White Rock-Spring Mountain Conservation Habitat Area"
  "Ipswich City Council Koala Conservation Plan"
  "2018"
  "https://www.ipswich.qld.gov.au/files/assets/public/v/1/about-council/initiatives/environment/wildlife/koala-conservation/documents/koala-conservation-plan.pdf"
  Source.governmentSource
  "Primary local-government conservation-planning source. It identifies White Rock-Spring Mountain as a large conservation estate within the Flinders-Karawatha bioregional wildlife corridor and describes that corridor as supporting fauna movement, migration and transfer of genetic diversity; it also identifies Springfield urban development on the estate's eastern/north-eastern fringe as a future threat context."
  Source.publicAttribution

qldKoalaMapping : Source.AttributedSource
qldKoalaMapping = Source.mkNoDOISource
  "Queensland Government"
  "Koala habitat maps for South East Queensland"
  "Queensland koala mapping / conservation planning guidance"
  "2026"
  "https://environment.qld.gov.au/wildlife/animals/living-with/koalas/mapping/koalamaps"
  Source.governmentSource
  "Primary state spatial-policy source. It defines Koala Priority Areas as large connected areas with the highest likelihood of sustaining SEQ koala populations in the long term and describes the modelling inputs used for core/local koala habitat. Used as a method/official spatial context source, not as proof that the exact Springview habitat is essential under NCA s 13."
  Source.publicAttribution

------------------------------------------------------------------------
-- Primary empirical / SOTA literature selected by the Snowball.
------------------------------------------------------------------------

mcalpine2006 : Source.AttributedSource
mcalpine2006 = Source.mkDOISource
  "Clive A. McAlpine; Michiala E. Bowen; John G. Callaghan; Daniel Lunney; Jonathan R. Rhodes; David L. Mitchell; David V. Pullar; Hugh P. Possingham"
  "Testing alternative models for the conservation of koalas in fragmented rural-urban landscapes"
  "Austral Ecology 31, 529-544"
  "2006"
  "10.1111/j.1442-9993.2006.01603.x"
  "https://doi.org/10.1111/j.1442-9993.2006.01603.x"
  Source.academicArticleSource
  "Primary empirical SEQ study. It found koala presence was best predicted by a multilevel combination including high-quality habitat proportion, neighbourhood effects, forest-patch spacing/density and sealed-road density. Used to define variables for local expert analysis, not to infer Springview occupancy or essentiality."
  Source.publicAttribution

rhodes2006 : Source.AttributedSource
rhodes2006 = Source.mkDOISource
  "Jonathan R. Rhodes; Clive A. McAlpine; Daniel Lunney; Hugh P. Possingham"
  "The importance of forest area and configuration relative to local habitat factors for conserving forest mammals: A case study of koalas in Queensland, Australia"
  "Biological Conservation 132(2), 153-165"
  "2006"
  "10.1016/j.biocon.2006.03.021"
  "https://doi.org/10.1016/j.biocon.2006.03.021"
  Source.academicArticleSource
  "Primary empirical Queensland koala study separating forest area/configuration from local habitat variables. Used for counterfactual and landscape-scale analysis, not as same-object Springview evidence."
  Source.publicAttribution

mclennan2025 : Source.AttributedSource
mclennan2025 = Source.mkDOISource
  "E. A. McLennan et al."
  "Genomics identifies koala populations at risk across eastern Australia"
  "Ecological Applications"
  "2025"
  "10.1002/eap.3062"
  "https://doi.org/10.1002/eap.3062"
  Source.academicArticleSource
  "Primary genomic study. It reports low genomic diversity/high recent inbreeding in several populations including coastal southeast Queensland and identifies major linear/sprawled infrastructure as barriers to koala dispersal. Used to sharpen the local population/gene-flow acquisition question, not to assign Springview to a genomic population without local samples."
  Source.publicAttribution

brunton2026 : Source.AttributedSource
brunton2026 = Source.mkDOISource
  "E. Brunton et al.; Romane H. Cristescu corresponding author"
  "Mapping connectivity for conservation of a threatened iconic mammal, the koala: Trends, challenges and opportunities"
  "Ecological Solutions and Evidence"
  "2026"
  "10.1002/2688-8319.70253"
  "https://doi.org/10.1002/2688-8319.70253"
  Source.academicArticleSource
  "Current systematic review of koala connectivity mapping. Used as SOTA methodological guidance: structural corridor maps should not be promoted into realised functional connectivity without appropriate validation."
  Source.publicAttribution

localPopulationNexusAtlas : Source.AttributedSourceAtlas
localPopulationNexusAtlas = Source.mkSourceAtlas
  "Woogaroo local koala population/connectivity Snowball"
  "DASHI.Law.SensibLawWoogarooLocalKoalaPopulationNexusSnowballExact"
  (ipswichWoogarooCatchment ∷ ipswichKoalaPlan ∷ qldKoalaMapping ∷
   mcalpine2006 ∷ rhodes2006 ∷ Population.lee2010 ∷ Population.dudaniec2013 ∷
   mclennan2025 ∷ brunton2026 ∷ [])
  "Primary local-government landscape sources plus primary empirical and current review literature. DOI/QID/Dewey coordinates are navigation/provenance coordinates; they do not manufacture same-object Springview population identity, functional connectivity, legal essentiality or Ministerial opinion."

------------------------------------------------------------------------
-- Ibrahim coordinates / traversal graph.
------------------------------------------------------------------------

localWoogarooPopulationCoordinate : Ibrahim.DashiKnowledgeCoordinate
localWoogarooPopulationCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooLocalKoalaPopulationNexusSnowballExact.agda"
  "Woogaroo/Opossum local urban-koala population and corridor context"
  koalaDewey
  (Id.rawItemId koalaQid)
  "Ipswich City Council primary local landscape sources"

localConnectivityCoordinate : Ibrahim.DashiKnowledgeCoordinate
localConnectivityCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooLocalKoalaPopulationNexusSnowballExact.agda"
  "Woogaroo/Opossum/White Rock-Spring Mountain functional-connectivity candidate"
  ecologyDewey
  (Id.rawItemId ecologicalConnectivityQid)
  "Ipswich Council corridor context + DOI:10.1111/mec.12359 + DOI:10.1002/2688-8319.70253"

fragmentationMechanismCoordinate : Ibrahim.DashiKnowledgeCoordinate
fragmentationMechanismCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooLocalKoalaPopulationNexusSnowballExact.agda"
  "koala habitat fragmentation / landscape configuration mechanism"
  ecologyDewey
  (Id.rawItemId habitatFragmentationQid)
  "doi:10.1111/j.1442-9993.2006.01603.x; doi:10.1016/j.biocon.2006.03.021"

landscapeEcologyCoordinate : Ibrahim.DashiKnowledgeCoordinate
landscapeEcologyCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooLocalKoalaPopulationNexusSnowballExact.agda"
  "landscape ecology parent"
  ecologyDewey
  (Id.rawItemId landscapeEcologyQid)
  "Q738011"

conservationBiologyCoordinate : Ibrahim.DashiKnowledgeCoordinate
conservationBiologyCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooLocalKoalaPopulationNexusSnowballExact.agda"
  "conservation biology parent"
  conservationBiologyDewey
  (Id.rawItemId conservationBiologyQid)
  "Q641498"

localToS13 : Ibrahim.DashiFirstLinkEdge
localToS13 = Ibrahim.dashi-first-link-edge
  localWoogarooPopulationCoordinate Canonical.s13EssentialityCoordinate Ibrahim.supportedBy
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Independent local-government material narrows the population nexus: Woogaroo/Opossum is officially described as important for securing urban koala populations and part of a regional corridor. It still does not identify the biologically relevant viable population or prove statutory essentiality."
  true

connectivityToS13 : Ibrahim.DashiFirstLinkEdge
connectivityToS13 = Ibrahim.dashi-first-link-edge
  localConnectivityCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Local corridor context plus regional landscape-genetics science identifies the exact empirical bridge still needed: realised local movement/gene flow and the without-site counterfactual."
  true

fragmentationToS102 : Ibrahim.DashiFirstLinkEdge
fragmentationToS102 = Ibrahim.dashi-first-link-edge
  fragmentationMechanismCoordinate Canonical.s102StatutoryCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Landscape-scale habitat loss/configuration/road mechanisms help structure the independent expert's likely-effect analysis; they are not the Queensland statutory conclusion."
  true

connectivityToLandscapeEcology : Ibrahim.DashiFirstLinkEdge
connectivityToLandscapeEcology = Ibrahim.dashi-first-link-edge
  localConnectivityCoordinate landscapeEcologyCoordinate Ibrahim.generalisesTo
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Ibrahim-style navigation from the local connectivity question to its landscape-ecology parent; navigation is not proof dependency."
  true

landscapeEcologyToConservation : Ibrahim.DashiFirstLinkEdge
landscapeEcologyToConservation = Ibrahim.dashi-first-link-edge
  landscapeEcologyCoordinate conservationBiologyCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Broader conservation-biology context for population viability and habitat-loss counterfactuals; no legal promotion."
  true

------------------------------------------------------------------------
-- Legal atom intersection.
------------------------------------------------------------------------

record LocalSourceAtomBinding : Set where
  constructor local-source-atom-binding
  field
    sourceLabel : String
    atom : Atom.LegalExecutionAtom
    consumer : Atom.LegalExecutionConsumer
    granularity : SourceGranularity
    independence : EvidenceIndependence
    admissible : Bool
    consumerComplete : Bool
    contribution : String
    residual : String

open LocalSourceAtomBinding public

councilPopulationToS13 : LocalSourceAtomBinding
councilPopulationToS13 = local-source-atom-binding
  "Ipswich City Council — Woogaroo Creek sub-catchment"
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  localLandscape independentInstitutional true false
  "Independent local institutional evidence that the Woogaroo/Opossum landscape is relevant to securing urban koala populations and forms part of a regional corridor."
  "Still identify the biological population/community and quantify whether Springview habitat is essential rather than merely relevant or connected."

whiteRockCorridorToS13 : LocalSourceAtomBinding
whiteRockCorridorToS13 = local-source-atom-binding
  "Ipswich City Council — White Rock-Spring Mountain Koala Conservation Habitat Area"
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  localLandscape independentInstitutional true false
  "Independent local planning/conservation evidence that the adjacent bioregional corridor is intended to permit movement, migration and transfer of genetic diversity."
  "Planning description of a corridor is not measured current movement or gene flow through the exact Springview habitat."

qldMappingToS13 : LocalSourceAtomBinding
qldMappingToS13 = local-source-atom-binding
  "Queensland Government — SEQ koala habitat mapping"
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  regionalSEQ independentInstitutional true false
  "Official methodology ties large connected areas to long-term population-sustaining likelihood and provides a state spatial prior for expert analysis."
  "Regulatory koala mapping does not itself satisfy the NCA s 13 essentiality definition for the Springview parcel."

localCouncilToS102 : LocalSourceAtomBinding
localCouncilToS102 = local-source-atom-binding
  "Ipswich City Council — Woogaroo/Opossum population/corridor context"
  Atom.likelySignificantDetrimentalEffectAtom
  Atom.nca102InterimOrderConsumer
  localLandscape independentInstitutional true false
  "Independent local context strengthens the causal relevance of fragmentation/connectivity loss to the threatened-wildlife consumer."
  "It does not establish likelihood, magnitude, duration, reversibility or mitigation-adjusted significant detrimental effect."

------------------------------------------------------------------------
-- Highest-alpha result.
------------------------------------------------------------------------

record LocalPopulationNexusState : Set where
  constructor local-population-nexus-state
  field
    independentLocalInstitutionalNexusPaid : Bool
    officialRegionalCorridorContextPaid : Bool
    populationSustainingSpatialMethodPaid : Bool
    primarySEQGeneticsMethodsPaid : Bool
    currentGenomicsRiskContextPaid : Bool
    exactBiologicalPopulationIdentityPaid : Bool
    realisedSpringviewFunctionalConnectivityPaid : Bool
    withoutSiteEssentialityCounterfactualPaid : Bool
    independentCurrentS102ExpertApplicationPaid : Bool
    nextAction : String

currentLocalPopulationNexusState : LocalPopulationNexusState
currentLocalPopulationNexusState = local-population-nexus-state
  true true true true true
  false false false false
  "The literature/local-institutional Snowball is now deep enough. Highest-alpha acquisition is a current independent ecologist opinion that (1) identifies the relevant local Koala population/community using available monitoring/telemetry/genetic/density evidence, (2) states whether Woogaroo/Opossum/Springview provides realised functional connectivity or a bottleneck, (3) runs the with-site/without-site counterfactual, and (4) separately applies the NCA ss 12/102 likely-significant-detrimental-effect wording to the approved 9281 process after mitigation."

------------------------------------------------------------------------
-- Dewey/QID/source attribution boundaries.
------------------------------------------------------------------------

data LocalGovernmentPopulationLanguageEqualsPopulationBoundary : Set where
data CorridorDesignationEqualsRealisedGeneFlow : Set where
data KoalaPriorityMethodEqualsNCA13Essentiality : Set where
data DOIEqualsSameObjectObservation : Set where
data QIDEqualsLegalElement : Set where
data DeweyClassEqualsProofDependency : Set where
data ReviewEqualsPrimaryLocalObservation : Set where

data OfficialMapEqualsCurrentHabitatCondition : Set where

councilLanguageDoesNotDefinePopulation : LocalGovernmentPopulationLanguageEqualsPopulationBoundary → ⊥
councilLanguageDoesNotDefinePopulation ()

corridorDoesNotCreateGeneFlow : CorridorDesignationEqualsRealisedGeneFlow → ⊥
corridorDoesNotCreateGeneFlow ()

qldMapDoesNotCreateS13Essentiality : KoalaPriorityMethodEqualsNCA13Essentiality → ⊥
qldMapDoesNotCreateS13Essentiality ()

doiDoesNotCreateSameObjectObservation : DOIEqualsSameObjectObservation → ⊥
doiDoesNotCreateSameObjectObservation ()

qidDoesNotCreateLegalElement : QIDEqualsLegalElement → ⊥
qidDoesNotCreateLegalElement ()

deweyDoesNotCreateProofDependency : DeweyClassEqualsProofDependency → ⊥
deweyDoesNotCreateProofDependency ()

reviewDoesNotBecomeLocalObservation : ReviewEqualsPrimaryLocalObservation → ⊥
reviewDoesNotBecomeLocalObservation ()

officialMapDoesNotBecomeCurrentCondition : OfficialMapEqualsCurrentHabitatCondition → ⊥
officialMapDoesNotBecomeCurrentCondition ()

------------------------------------------------------------------------
-- Existing acquisition owner remains authoritative for the open leaves.
------------------------------------------------------------------------

populationAcquisitionLeaf : Acquisition.AcquisitionLeafReceipt
populationAcquisitionLeaf = Acquisition.s13PopulationLeaf

functionalConnectivityAcquisitionLeaf : Acquisition.AcquisitionLeafReceipt
functionalConnectivityAcquisitionLeaf = Acquisition.functionalConnectivityLeaf

s102ExpertAcquisitionLeaf : Acquisition.AcquisitionLeafReceipt
s102ExpertAcquisitionLeaf = Acquisition.s102ExpertOpinionLeaf
