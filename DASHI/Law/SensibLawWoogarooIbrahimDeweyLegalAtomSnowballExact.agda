module DASHI.Law.SensibLawWoogarooIbrahimDeweyLegalAtomSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Ontology.DeweyQidCoverageQualityExact as Coverage
import DASHI.Law.SensibLawWoogarooEvidenceDependencyMatrixExact as Dependency
import DASHI.Law.SensibLawWoogarooS102LikelySignificantDetrimentalEffectCaseExact as S102
import DASHI.Law.SensibLawWoogarooS13EssentialityStressTestExact as S13

------------------------------------------------------------------------
-- WOOGAROO × IBRAHIM / DEWEY / QID / LEGAL-ATOM SNOWBALL
--
-- Ibrahim's First Link Network is used here as a discovery discipline:
-- traverse outward and upward from a concrete consumer, preserve source identity,
-- and keep navigation separate from truth or legal sufficiency.  No current
-- Wikipedia first-link edge is promoted to a historical November-2014 FLN edge
-- unless independently reproduced against the Ibrahim parser/snapshot.
------------------------------------------------------------------------

data SourceRole : Set where
  methodPrimary : SourceRole
  empiricalPrimary : SourceRole
  reviewSecondary : SourceRole
  governmentPrimary : SourceRole
  ontologyCoordinate : SourceRole

data MetadataState : Set where
  paid : MetadataState
  unresolved : MetadataState
  notApplicable : MetadataState

record SnowballSourceCoordinate : Set where
  constructor snowball-source-coordinate
  field
    source : Source.AttributedSource
    role : SourceRole
    doi : String
    doiState : MetadataState
    publicationQid : String
    publicationQidState : MetadataState
    subjectQid : String
    subjectQidState : MetadataState
    dewey : String
    deweyState : MetadataState
    primaryLink : String
    legalConsumer : String
    exactUse : String
    promotionBoundary : String

open SnowballSourceCoordinate public

------------------------------------------------------------------------
-- Method source: Ibrahim et al.
------------------------------------------------------------------------

ibrahimSource : Source.AttributedSource
ibrahimSource = Source.mkDOISource
  "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds"
  "Connecting every bit of knowledge: The structure of Wikipedia's First Link Network"
  "Journal of Computational Science 19 (2017), 21-30"
  "2017"
  "10.1016/j.jocs.2016.12.001"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  Source.academicArticleSource
  "Methodological source for first-link traversal, accumulation and traversal-funnel discovery. Used only as a navigation/search method for Woogaroo evidence and concept acquisition."
  Source.publicAttribution

ibrahimCoordinate : SnowballSourceCoordinate
ibrahimCoordinate = snowball-source-coordinate
  ibrahimSource methodPrimary
  "10.1016/j.jocs.2016.12.001" paid
  "unresolved" unresolved
  "Q328798 / Q641498 / Q738011 depending traversed topic; no single paper-topic QID asserted" unresolved
  "unresolved for the publication itself; topic Dewey coordinates are carried separately" unresolved
  "https://compstorylab.org/share/papers/ibrahim2016a/paper/2015-11-wikipedia-network.pdf"
  "evidence discovery / source archaeology"
  "Follow concept/source edges from legal residuals, then return to primary scientific or statutory carriers before payment."
  "First-link reachability, QID adjacency and Dewey proximity are discovery coordinates only; none creates legal or scientific authority."

------------------------------------------------------------------------
-- Current highest-alpha ecology sources reached by the Snowball.
------------------------------------------------------------------------

brunton2026Source : Source.AttributedSource
brunton2026Source = Source.mkDOISource
  "Elizabeth A. Brunton; Katrin Hohwieler; Kye McDonald; Romane H. Cristescu"
  "Mapping connectivity for conservation of a threatened iconic mammal, the koala: Trends, challenges and opportunities"
  "Ecological Solutions and Evidence 7 (2026), e70253"
  "2026"
  "10.1002/2688-8319.70253"
  "https://doi.org/10.1002/2688-8319.70253"
  Source.academicArticleSource
  "Current systematic review of koala connectivity mapping; identifies the gap between potential connectivity maps and realised functional connectivity, local-population calibration and field validation."
  Source.publicAttribution

brunton2026Coordinate : SnowballSourceCoordinate
brunton2026Coordinate = snowball-source-coordinate
  brunton2026Source reviewSecondary
  "10.1002/2688-8319.70253" paid
  "unresolved" unresolved
  "Q2993449" paid
  "577 / 333.95" paid
  "https://besjournals.onlinelibrary.wiley.com/doi/10.1002/2688-8319.70253"
  "s 13 viable-population/essentiality and s 102 significant-detrimental-effect evidence design"
  "Raises the evidentiary priority of realised functional connectivity, local population data and validation over another unvalidated corridor map."
  "A review identifies method limitations and evidence priorities; it does not establish Woogaroo connectivity, population identity or legal essentiality."

mcalpine2006Source : Source.AttributedSource
mcalpine2006Source = Source.mkDOISource
  "Clive McAlpine et al."
  "The importance of forest area and configuration relative to local habitat factors for conserving forest mammals: A case study of koalas in Queensland, Australia"
  "Biological Conservation 132 (2006), 153-165"
  "2006"
  "10.1016/j.biocon.2006.03.021"
  "https://doi.org/10.1016/j.biocon.2006.03.021"
  Source.academicArticleSource
  "Primary empirical southeast-Queensland koala study testing forest area/configuration, roads and local habitat factors in a fragmented rural-urban landscape."
  Source.publicAttribution

mcalpine2006Coordinate : SnowballSourceCoordinate
mcalpine2006Coordinate = snowball-source-coordinate
  mcalpine2006Source empiricalPrimary
  "10.1016/j.biocon.2006.03.021" paid
  "unresolved" unresolved
  "Q913302" paid
  "577.27" paid
  "https://doi.org/10.1016/j.biocon.2006.03.021"
  "s 102 causal pathway; s 13 connectivity/function background"
  "Independent regional empirical evidence that forest area/configuration and fragmentation matter to koala occurrence in southeast Queensland."
  "Regional empirical relevance is not same-object proof for Springview/Woogaroo and does not identify the local viable population."

rus2021Source : Source.AttributedSource
rus2021Source = Source.mkDOISource
  "A. I. Rus; C. McArthur; V. S. A. Mella; M. S. Crowther"
  "Habitat fragmentation affects movement and space use of a specialist folivore, the koala"
  "Animal Conservation 24 (2021), 26-37"
  "2021"
  "10.1111/acv.12596"
  "https://doi.org/10.1111/acv.12596"
  Source.academicArticleSource
  "Primary GPS-tracking study connecting reduced functional connectivity with altered koala movement and space use."
  Source.publicAttribution

rus2021Coordinate : SnowballSourceCoordinate
rus2021Coordinate = snowball-source-coordinate
  rus2021Source empiricalPrimary
  "10.1111/acv.12596" paid
  "unresolved" unresolved
  "Q2993449" paid
  "577.27" paid
  "https://doi.org/10.1111/acv.12596"
  "s 102 causal pathway; s 13 without-site connectivity counterfactual"
  "Provides empirical support for treating functional connectivity as a biological process variable rather than a purely cartographic label."
  "The study site is not Woogaroo; effect size and local applicability require independent same-object evidence."

dennison2016Source : Source.AttributedSource
dennison2016Source = Source.mkDOISource
  "S. Dennison; G. J. Frankham; L. E. Neaves; C. Flanagan; S. Fitzgibbon; M. D. B. Eldridge; R. N. Johnson"
  "Population genetics of the koala (Phascolarctos cinereus) in north-eastern New South Wales and south-eastern Queensland"
  "Australian Journal of Zoology 64 (2016), 402-412"
  "2016"
  "10.1071/ZO16081"
  "https://doi.org/10.1071/ZO16081"
  Source.academicArticleSource
  "Primary regional population-genetics source for population structure and gene-flow questions across southeast Queensland."
  Source.publicAttribution

dennison2016Coordinate : SnowballSourceCoordinate
dennison2016Coordinate = snowball-source-coordinate
  dennison2016Source empiricalPrimary
  "10.1071/ZO16081" paid
  "unresolved" unresolved
  "Q31151" paid
  "576.58" paid
  "https://doi.org/10.1071/ZO16081"
  "s 13 viable-population identity"
  "Supports the next acquisition question: define a biologically meaningful population independently of the development boundary, using regional population structure/gene-flow evidence where applicable."
  "Regional population-genetics evidence does not automatically place Springview animals in a particular population cluster; same-object/local evidence remains required."

koalaHabitatGuidanceSource : Source.AttributedSource
koalaHabitatGuidanceSource = Source.mkNoDOISource
  "Department of Climate Change, Energy, the Environment and Water"
  "Identifying habitat for the endangered Koala"
  "Australian Government threatened-species guidance"
  "2025"
  "https://www.dcceew.gov.au/environment/epbc/publications/identifying-habitat-for-the-endangered-koala"
  Source.governmentSource
  "Primary current federal guidance describing habitat attributes including feed trees, connectivity and proximity to koala populations; used as guidance/context rather than a Queensland s 13 legal definition."
  Source.publicAttribution

koalaHabitatGuidanceCoordinate : SnowballSourceCoordinate
koalaHabitatGuidanceCoordinate = snowball-source-coordinate
  koalaHabitatGuidanceSource governmentPrimary
  "not applicable" notApplicable
  "unresolved" unresolved
  "Q36101" paid
  "599.25" paid
  "https://www.dcceew.gov.au/environment/epbc/publications/identifying-habitat-for-the-endangered-koala"
  "ecological habitat attributes for s 102/s 13 evidence design"
  "Supplies a current government ecology/guidance coordinate for koala habitat attributes."
  "Federal habitat guidance is not the Queensland NCA s 13 essentiality test and does not establish same-object habitat facts."

------------------------------------------------------------------------
-- QID / Dewey concept graph.  These are semantic/search coordinates.
------------------------------------------------------------------------

data LegalEcologyConcept : Set where
  koala
  endangeredSpecies
  habitatFragmentation
  ecologicalConnectivity
  wildlifeCorridor
  landscapeEcology
  conservationBiology
  populationGenetics
  geneFlow
  environmentalLaw
  environmentalImpactAssessment : LegalEcologyConcept

record ConceptCoordinate : Set where
  constructor concept-coordinate
  field
    concept : LegalEcologyConcept
    qid : String
    qidPaid : Bool
    dewey : String
    deweyPaid : Bool
    coordinateLink : String
    legalAtomUse : String

open ConceptCoordinate public

koalaConcept : ConceptCoordinate
koalaConcept = concept-coordinate koala "Q36101" true "599.25" true "https://www.wikidata.org/wiki/Q36101" "qualifying threatened wildlife / species identity"
endangeredConcept : ConceptCoordinate
endangeredConcept = concept-coordinate endangeredSpecies "Q11394" true "333.95" true "https://www.wikidata.org/wiki/Q11394" "conservation-status search coordinate; official Queensland listing remains authoritative for the legal status atom"
fragmentationConcept : ConceptCoordinate
fragmentationConcept = concept-coordinate habitatFragmentation "Q913302" true "577.27" true "https://www.wikidata.org/wiki/Q913302" "causal pathway: clearing -> fragmentation -> movement/habitat-function effects"
connectivityConcept : ConceptCoordinate
connectivityConcept = concept-coordinate ecologicalConnectivity "Q2993449" true "577" true "https://www.wikidata.org/wiki/Q2993449" "s 13 functional-connectivity and s 102 causal-effect evidence"
corridorConcept : ConceptCoordinate
corridorConcept = concept-coordinate wildlifeCorridor "Q864912" true "577" true "https://www.wikidata.org/wiki/Q864912" "corridor evidence discovery; corridor label alone does not pay essentiality"
landscapeEcologyConcept : ConceptCoordinate
landscapeEcologyConcept = concept-coordinate landscapeEcology "Q738011" true "577" true "https://www.wikidata.org/wiki/Q738011" "landscape-scale counterfactual and fragmentation analysis"
conservationBiologyConcept : ConceptCoordinate
conservationBiologyConcept = concept-coordinate conservationBiology "Q641498" true "333.95" true "https://www.wikidata.org/wiki/Q641498" "population viability / conservation evidence discovery"
populationGeneticsConcept : ConceptCoordinate
populationGeneticsConcept = concept-coordinate populationGenetics "Q31151" true "576.58" true "https://www.wikidata.org/wiki/Q31151" "identify viable population structure independently of development boundary"
geneFlowConcept : ConceptCoordinate
geneFlowConcept = concept-coordinate geneFlow "Q143089" true "576.58" true "https://www.wikidata.org/wiki/Q143089" "connectivity/population exchange evidence"
environmentalLawConcept : ConceptCoordinate
environmentalLawConcept = concept-coordinate environmentalLaw "Q328798" true "344.046" true "https://www.wikidata.org/wiki/Q328798" "statutory consumer / legal doctrine navigation only"
environmentalImpactConcept : ConceptCoordinate
environmentalImpactConcept = concept-coordinate environmentalImpactAssessment "Q320389" true "unresolved" false "https://www.wikidata.org/wiki/Q320389" "federal assessment-document/source discovery"

------------------------------------------------------------------------
-- Ibrahim-style traversal edges for acquisition.  These are NOT asserted as
-- literal historical Wikipedia first-link edges.
------------------------------------------------------------------------

data DiscoveryRelation : Set where
  topicNeighbour
  evidenceProducerFor
  legalConsumerNeeds
  sameObjectJoinNeeded
  firstLinkHistoricalUnpaid : DiscoveryRelation

record DiscoveryEdge : Set where
  constructor discovery-edge
  field
    fromConcept : LegalEcologyConcept
    toConcept : LegalEcologyConcept
    relation : DiscoveryRelation
    priority : String
    why : String
    promotesLegalConclusion : Bool

open DiscoveryEdge public

populationToConnectivity : DiscoveryEdge
populationToConnectivity = discovery-edge
  populationGenetics ecologicalConnectivity evidenceProducerFor
  "highest"
  "s 13 first needs a biologically meaningful population; realised connectivity/gene-flow evidence is a stronger bridge than another static corridor map."
  false

connectivityToFragmentation : DiscoveryEdge
connectivityToFragmentation = discovery-edge
  ecologicalConnectivity habitatFragmentation evidenceProducerFor
  "highest"
  "s 102/s 13 need the causal counterfactual: what clearing/severance does to movement and habitat function."
  false

koalaToPopulation : DiscoveryEdge
koalaToPopulation = discovery-edge
  koala populationGenetics legalConsumerNeeds
  "highest"
  "move from species identity/occurrence to the relevant viable population/community required by s 13."
  false

corridorToConnectivity : DiscoveryEdge
corridorToConnectivity = discovery-edge
  wildlifeCorridor ecologicalConnectivity sameObjectJoinNeeded
  "high"
  "replace corridor-label reasoning with realised/potential functional-connectivity evidence on the exact landscape."
  false

lawToEcology : DiscoveryEdge
lawToEcology = discovery-edge
  environmentalLaw conservationBiology legalConsumerNeeds
  "high"
  "the legal consumer specifies the proposition to be paid; ecology supplies evidence but does not create the legal conclusion."
  false

------------------------------------------------------------------------
-- Highest-alpha conclusion from the 2026 review snowball.
------------------------------------------------------------------------

record HighestAlphaEcologyCut : Set where
  constructor highest-alpha-ecology-cut
  field
    anotherStaticCorridorMapHighestAlpha : Bool
    realisedFunctionalConnectivityEvidenceHighestAlpha : Bool
    localPopulationIdentityHighestAlpha : Bool
    currentIndependentEffectOpinionHighestAlpha : Bool
    exactNextSearch : String

currentHighestAlphaEcologyCut : HighestAlphaEcologyCut
currentHighestAlphaEcologyCut = highest-alpha-ecology-cut
  false
  true
  true
  true
  "Search for, in order: (1) telemetry/genetic/local-population evidence that can locate the Woogaroo/Springfield koala population or realised movement network; (2) current independent ecological opinion applying s 102 to A12705838 and current habitat; (3) field validation of connectivity/occurrence; only then add more potential-connectivity mapping."

------------------------------------------------------------------------
-- Intersection with existing legal/atom machinery.
------------------------------------------------------------------------

record LegalAtomIntersection : Set where
  constructor legal-atom-intersection
  field
    consumer : String
    sourcePaidInput : String
    sourceDependencyWarning : String
    firstUnpaidAtom : String
    snowballDirection : String

open LegalAtomIntersection public

s102Intersection : LegalAtomIntersection
s102Intersection = legal-atom-intersection
  "NCA s 102 likely significant detrimental effect"
  "Koala threatened status; approved 9281 clearing/earthworks process; SHG occurrence/connectivity/significant-impact propositions; current statutory text"
  "Multiple SHG propositions share one upstream proponent-side ecology lineage and are not independent corroboration."
  "current independent ecological effect opinion on the actual approved/current state"
  "fragmentation -> functional connectivity -> movement/population effect -> likely significant detrimental effect"

s13Intersection : LegalAtomIntersection
s13Intersection = legal-atom-intersection
  "NCA s 13 essentiality to a viable population/community"
  "same-project habitat function/connectivity plus regional koala/connectivity literature"
  "static map agreement is not independent proof of realised functional connectivity or population identity."
  "independently identify the viable population/community and join it to the Springview/Woogaroo habitat counterfactual"
  "koala -> population genetics/gene flow -> realised connectivity -> without-site counterfactual -> essentiality"

------------------------------------------------------------------------
-- Source atlas.
------------------------------------------------------------------------

woogarooIbrahimDeweySourceAtlas : Source.AttributedSourceAtlas
woogarooIbrahimDeweySourceAtlas = Source.mkSourceAtlas
  "Woogaroo Ibrahim/Dewey/QID legal-atom snowball source atlas"
  "DASHI.Law.SensibLawWoogarooIbrahimDeweyLegalAtomSnowballExact"
  (ibrahimSource ∷ brunton2026Source ∷ mcalpine2006Source ∷ rus2021Source ∷ dennison2016Source ∷ koalaHabitatGuidanceSource ∷ [])
  "Method source plus current review, independent empirical connectivity/population sources and government guidance. DOI/QID/Dewey metadata are search/provenance coordinates; they do not import proof or authority."

------------------------------------------------------------------------
-- Reuse current consumer states.
------------------------------------------------------------------------

s102Current : S102.S102CaseState
s102Current = S102.currentS102CaseState

s13Current : S13.S13StressTest
s13Current = S13.currentS13StressTest

dependencyS102 : Dependency.ConsumerDependencyState
dependencyS102 = Dependency.s102DependencyState

dependencyS13 : Dependency.ConsumerDependencyState
dependencyS13 = Dependency.s13DependencyState

coverageBoundary : Coverage.CoverageQualityBoundary
coverageBoundary = Coverage.canonicalCoverageQualityBoundary

------------------------------------------------------------------------
-- No-promotion boundaries.
------------------------------------------------------------------------

data QidEqualsAuthority : Set where
data DeweyEqualsEvidence : Set where
data DoiEqualsIndependentCorroboration : Set where
data ReviewEqualsSameObjectObservation : Set where
data FirstLinkEqualsLegalDependence : Set where
data ConnectivityMapEqualsRealisedConnectivity : Set where
data RegionalStudyEqualsWoogarooPopulationIdentity : Set where

qidDoesNotCreateAuthority : QidEqualsAuthority → ⊥
qidDoesNotCreateAuthority ()

deweyDoesNotCreateEvidence : DeweyEqualsEvidence → ⊥
deweyDoesNotCreateEvidence ()

doiDoesNotCreateIndependentCorroboration : DoiEqualsIndependentCorroboration → ⊥
doiDoesNotCreateIndependentCorroboration ()

reviewDoesNotCreateSameObjectObservation : ReviewEqualsSameObjectObservation → ⊥
reviewDoesNotCreateSameObjectObservation ()

firstLinkDoesNotCreateLegalDependence : FirstLinkEqualsLegalDependence → ⊥
firstLinkDoesNotCreateLegalDependence ()

connectivityMapDoesNotBecomeRealisedConnectivity : ConnectivityMapEqualsRealisedConnectivity → ⊥
connectivityMapDoesNotBecomeRealisedConnectivity ()

regionalStudyDoesNotIdentifyWoogarooPopulation : RegionalStudyEqualsWoogarooPopulationIdentity → ⊥
regionalStudyDoesNotIdentifyWoogarooPopulation ()
