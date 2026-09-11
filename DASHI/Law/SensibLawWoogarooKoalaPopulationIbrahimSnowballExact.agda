module DASHI.Law.SensibLawWoogarooKoalaPopulationIbrahimSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Wikimedia.IdentifierExact as WikiId
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom
import DASHI.Law.SensibLawWoogarooEvidenceDependencyMatrixExact as Dependency

------------------------------------------------------------------------
-- WOOGAROO KOALA POPULATION / CONNECTIVITY IBRAHIM SNOWBALL
--
-- Purpose:
--   turn the newly located Ipswich monitoring / IKPS / peer-reviewed method
--   lineage into an attributed acquisition graph that another worker can use
--   directly for the s 13 viable-population/essentiality and s 102 likely-
--   significant-detrimental-effect consumers.
--
-- Ibrahim discipline:
--   author/title/DOI/source identity, QID and Dewey coordinates are retained;
--   graph adjacency never imports proof, authority or legal satisfaction.
------------------------------------------------------------------------

data SourceRole : Set where
  primaryLocalMonitoring : SourceRole
  primaryLocalRecordCustodian : SourceRole
  peerReviewedMethod : SourceRole
  peerReviewedStateOfArtReview : SourceRole
  peerReviewedDetectionMethod : SourceRole

data IdentifierState : Set where
  resolved : IdentifierState
  unresolved : IdentifierState
  notApplicable : IdentifierState

record IbrahimSourceCoordinate : Set where
  constructor ibrahim-source-coordinate
  field
    label : String
    role : SourceRole
    attributed : Source.AttributedSource
    doiText : String
    doiStatus : IdentifierState
    primaryQid : String
    qidStatus : IdentifierState
    deweyParent : String
    deweyStatus : IdentifierState
    projectOrPlace : String
    legalUse : String
    acquisitionResidual : String

open IbrahimSourceCoordinate public

biolink2020Source : Source.AttributedSource
biolink2020Source = Source.mkNoDOISource
  "Biolink Ecological Consultants Pty Ltd"
  "Ipswich baseline koala survey"
  "Biolink project page; project undertaken for Ipswich City Council"
  "2020"
  "https://biolink.com.au/ipswich-baseline-koala-survey/"
  Source.practitionerSource
  "Primary practitioner description of the 2020 Ipswich baseline survey: 63 SAT/Rapid-SAT sites across Mount Grandchester, Flinders-Goolman and White Rock-Spring Mountain, designed as a baseline for longer-term LGA monitoring. Used as monitoring-series identity/method evidence, not as a substitute for the underlying report or site-level data."
  Source.publicAttribution

biolink2025Source : Source.AttributedSource
biolink2025Source = Source.mkNoDOISource
  "Biolink Ecological Consultants Pty Ltd"
  "Ipswich Biennial koala survey and Population Change Analysis"
  "Biolink project page; third monitoring round for Ipswich Local Government Area"
  "2025"
  "https://biolink.com.au/ipswich-biennial-koala-survey-and-population-change-analysis/"
  Source.practitionerSource
  "Primary practitioner description of the third Ipswich monitoring round following 2020 and 2023: 83 permanent Council-estate sites plus 10 private conservation-agreement properties, with repeat activity/distribution analysis. Used to establish existence and design of the longitudinal series, not unpublished site-level findings."
  Source.publicAttribution

ikpsSource : Source.AttributedSource
ikpsSource = Source.mkNoDOISource
  "Ipswich Koala Protection Society Inc."
  "Ipswich Koala Protection Society — local koala records, statistics and mapping"
  "IKPS official website"
  "2026"
  "https://www.ikps.org.au/about.htm"
  Source.communitySource
  "Primary organisational source that IKPS maintains extensive local koala records, statistics and habitat/population mapping and operates a long-running rescue service. Used as an acquisition lead for an independent local observational record stream; not treated as already-acquired raw records or an expert population analysis."
  Source.publicAttribution

mcalpine2006Source : Source.AttributedSource
mcalpine2006Source = Source.mkDOISource
  "Clive A. McAlpine; Jonathan R. Rhodes; John G. Callaghan; Michiala E. Bowen; Daniel Lunney; David L. Mitchell; David V. Pullar; Hugh P. Possingham"
  "The importance of forest area and configuration relative to local habitat factors for conserving forest mammals: A case study of koalas in Queensland, Australia"
  "Biological Conservation 132(2):153-165"
  "2006"
  "10.1016/j.biocon.2006.03.021"
  "https://doi.org/10.1016/j.biocon.2006.03.021"
  Source.academicArticleSource
  "Peer-reviewed southeast-Queensland method/evidence lineage showing that forest area, configuration, roads and local food-tree factors jointly relate to koala occurrence in fragmented rural-urban landscapes. Used as a general scientific bridge for fragmentation/connectivity mechanisms, not as site-specific Woogaroo evidence."
  Source.publicAttribution

brunton2026Source : Source.AttributedSource
brunton2026Source = Source.mkDOISource
  "Elizabeth A. Brunton; Katrin Hohwieler; Kye McDonald; Romane H. Cristescu"
  "Mapping connectivity for conservation of a threatened iconic mammal, the koala: Trends, challenges and opportunities"
  "Ecological Solutions and Evidence 7(2):e70253"
  "2026"
  "10.1002/2688-8319.70253"
  "https://doi.org/10.1002/2688-8319.70253"
  Source.academicArticleSource
  "2026 peer-reviewed state-of-the-art review of koala connectivity mapping. Used to calibrate evidentiary quality: it reports major heterogeneity in methods, limited local-population inputs and field validation, and no realised functional-connectivity mapping among reviewed koala studies through 2024."
  Source.publicAttribution

ellis2026ThermalSource : Source.AttributedSource
ellis2026ThermalSource = Source.mkDOISource
  "William Anthony Ellis; Madeleine Jennifer Harding; Sean Ian FitzGibbon; Amber Kristen Gillett; Benjamin James Barth"
  "Using thermal drones to validate historical koala surveys"
  "Australian Mammalogy 48(1):AM25037"
  "2026"
  "10.1071/AM25037"
  "https://doi.org/10.1071/AM25037"
  Source.academicArticleSource
  "Recent UQ-led detection-method paper comparing historical survey approaches with thermal-drone surveys. Used as a method-validation lead for future current-population acquisition, not as evidence that Woogaroo currently contains a particular population size."
  Source.publicAttribution

sparkes2025Source : Source.AttributedSource
sparkes2025Source = Source.mkDOISource
  "Gabriella R. Sparkes; Oakleigh Wilson; William A. Ellis; Sean I. FitzGibbon; Benjamin J. Barth; Christofer J. Clemente; Mathew S. Crowther; Robbie S. Wilson"
  "Between the Trees: Quantifying Koala Ground Movement for Conservation Action"
  "Animals 15(24):3537"
  "2025"
  "10.3390/ani15243537"
  "https://doi.org/10.3390/ani15243537"
  Source.academicArticleSource
  "Recent UQ/USC movement-ecology evidence on infrequent but high-risk ground travel between trees in fragmented landscapes. Used only to inform mechanism and expert questions about severance, road/interface risk and movement; not site-specific Woogaroo movement evidence."
  Source.publicAttribution

koalaQid : WikiId.ItemId
koalaQid = WikiId.itemId "Q36101"

ecologicalConnectivityQid : WikiId.ItemId
ecologicalConnectivityQid = WikiId.itemId "Q2993449"

landscapeEcologyQid : WikiId.ItemId
landscapeEcologyQid = WikiId.itemId "Q738011"

conservationBiologyQid : WikiId.ItemId
conservationBiologyQid = WikiId.itemId "Q641498"

ipswichQid : WikiId.ItemId
ipswichQid = WikiId.itemId "Q1631867"

springfieldQid : WikiId.ItemId
springfieldQid = WikiId.itemId "Q1838932"

biolink2020Coordinate : IbrahimSourceCoordinate
biolink2020Coordinate = ibrahim-source-coordinate
  "Biolink Ipswich baseline koala survey 2020"
  primaryLocalMonitoring
  biolink2020Source
  "none recorded by atlas"
  notApplicable
  "Q1631867 (City of Ipswich); Q36101 (koala)"
  resolved
  "599.25 (koala) / 577 (ecology)"
  resolved
  "Ipswich LGA, including White Rock-Spring Mountain Conservation Estate"
  "Candidate independent local-population/occupancy lineage for s 13 population identity and current/background s 102 exposure context."
  "Acquire the actual 2020 report/data and permanent-site identities; project-page metadata does not expose the site-level observations needed for the Woogaroo-facing join."

biolink2025Coordinate : IbrahimSourceCoordinate
biolink2025Coordinate = ibrahim-source-coordinate
  "Biolink Ipswich biennial survey / Population Change Analysis 2025"
  primaryLocalMonitoring
  biolink2025Source
  "none recorded by atlas"
  notApplicable
  "Q1631867 (City of Ipswich); Q36101 (koala)"
  resolved
  "599.25 (koala) / 577 (ecology)"
  resolved
  "Ipswich LGA; 83 permanent Council sites + 10 conservation-agreement properties"
  "Highest-value longitudinal acquisition candidate for independently identifying population/activity change near the White Rock-Spring Mountain / Springfield interface."
  "Acquire the 2023 and 2025 report bodies/data and identify which permanent sites are spatially relevant to Springview/Woogaroo; existence of the series does not pay local site findings."

ikpsCoordinate : IbrahimSourceCoordinate
ikpsCoordinate = ibrahim-source-coordinate
  "IKPS local rescue/sighting/release record base"
  primaryLocalRecordCustodian
  ikpsSource
  "none recorded by atlas"
  notApplicable
  "Q1631867 (City of Ipswich); Q36101 (koala)"
  resolved
  "599.25 (koala) / 333.95 (biological resources/conservation)"
  resolved
  "Ipswich and surrounding local koala landscape"
  "Potential observationally independent stream for population occurrence, movement, mortality and rescue/release geography; can test whether consultancy/project ecology is missing local records."
  "Request/export date-stamped records and mapping for the relevant Springview, Brookwater, Opossum Creek, Woogaroo Creek and White Rock-Spring Mountain interface; keep rescue, sighting and release event types distinct."

mcalpineCoordinate : IbrahimSourceCoordinate
mcalpineCoordinate = ibrahim-source-coordinate
  "McAlpine et al. 2006 forest configuration / koala occurrence"
  peerReviewedMethod
  mcalpine2006Source
  "10.1016/j.biocon.2006.03.021"
  resolved
  "Q36101; Q2993449; Q738011"
  resolved
  "577 (ecology/landscape ecology); 599.25 (koala)"
  resolved
  "fragmented rural-urban southeast Queensland"
  "General mechanism source for habitat area/configuration/roads and occurrence; informs expert counterfactual design for s 13 and likely-effect mechanism for s 102."
  "Do not count as an independent observation of Woogaroo; use only as scientific method/mechanism support unless same-object data are separately acquired."

bruntonCoordinate : IbrahimSourceCoordinate
bruntonCoordinate = ibrahim-source-coordinate
  "Brunton et al. 2026 koala connectivity SOTA review"
  peerReviewedStateOfArtReview
  brunton2026Source
  "10.1002/2688-8319.70253"
  resolved
  "Q36101; Q2993449; Q738011; Q641498"
  resolved
  "577 (ecology/landscape ecology); 333.95 (conservation biology)"
  resolved
  "koala connectivity literature through 2024"
  "Calibrates the evidentiary burden for any Woogaroo connectivity claim: structural/potential connectivity maps should be distinguished from realised functional connectivity and should be locally validated where possible."
  "Use the review to design acquisition/validation, not to infer that any particular Woogaroo corridor is realised functional connectivity."

ellisThermalCoordinate : IbrahimSourceCoordinate
ellisThermalCoordinate = ibrahim-source-coordinate
  "Ellis et al. 2026 thermal-drone validation"
  peerReviewedDetectionMethod
  ellis2026ThermalSource
  "10.1071/AM25037"
  resolved
  "Q36101; Q641498"
  resolved
  "599.25 (koala); 577 (ecology)"
  resolved
  "Queensland koala survey-method validation"
  "Future acquisition method for current independent detection/population estimation if existing longitudinal records leave a decisive local uncertainty."
  "Detection-method performance elsewhere does not establish Woogaroo occupancy or abundance."

sparkesCoordinate : IbrahimSourceCoordinate
sparkesCoordinate = ibrahim-source-coordinate
  "Sparkes et al. 2025 koala ground movement"
  peerReviewedMethod
  sparkes2025Source
  "10.3390/ani15243537"
  resolved
  "Q36101; Q2993449"
  resolved
  "599.25 (koala); 591.51 (behavioural ecology)"
  resolved
  "fragmented southeast-Queensland landscape"
  "Supports expert questions about whether fragmentation/severance increases risky ground movement and interface exposure; useful for mechanism, not direct Woogaroo effect magnitude."
  "No transport from general movement ecology to a site-specific legal conclusion without a same-object ecological join."

koalaPopulationSourceAtlas : Source.AttributedSourceAtlas
koalaPopulationSourceAtlas = Source.mkSourceAtlas
  "Woogaroo koala population / connectivity Ibrahim Snowball atlas"
  "DASHI.Law.SensibLawWoogarooKoalaPopulationIbrahimSnowballExact"
  (biolink2020Source ∷ biolink2025Source ∷ ikpsSource ∷ mcalpine2006Source ∷ brunton2026Source ∷ ellis2026ThermalSource ∷ sparkes2025Source ∷ [])
  "Local monitoring and record-custodian sources are separated from general peer-reviewed mechanism/method sources. DOI/QID/Dewey coordinates aid traversal only; no coordinate imports proof, legal authority or site-specific observation."

------------------------------------------------------------------------
-- Ibrahim first-link coordinates and edges.
------------------------------------------------------------------------

s13KnowledgeNode : Ibrahim.DashiKnowledgeCoordinate
s13KnowledgeNode = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooS13EssentialityStressTestExact.agda"
  "DASHI.Law.SensibLawWoogarooS13EssentialityStressTestExact"
  "333.95"
  "Q641498"
  "NCA-s13-primary-law"

s102KnowledgeNode : Ibrahim.DashiKnowledgeCoordinate
s102KnowledgeNode = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooS102LikelySignificantDetrimentalEffectCaseExact.agda"
  "DASHI.Law.SensibLawWoogarooS102LikelySignificantDetrimentalEffectCaseExact"
  "333.95"
  "Q641498"
  "NCA-s102-primary-law"

populationEvidenceNode : Ibrahim.DashiKnowledgeCoordinate
populationEvidenceNode = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooKoalaPopulationIbrahimSnowballExact.agda"
  "DASHI.Law.SensibLawWoogarooKoalaPopulationIbrahimSnowballExact"
  "599.25"
  "Q36101"
  "Biolink-2020-2025-and-IKPS"

connectivityMethodNode : Ibrahim.DashiKnowledgeCoordinate
connectivityMethodNode = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooKoalaPopulationIbrahimSnowballExact.agda#connectivity"
  "McAlpine-2006 / Brunton-2026"
  "577"
  "Q2993449"
  "10.1016/j.biocon.2006.03.021;10.1002/2688-8319.70253"

populationSupportsS13 : Ibrahim.DashiFirstLinkEdge
populationSupportsS13 = Ibrahim.dashi-first-link-edge
  populationEvidenceNode s13KnowledgeNode Ibrahim.supportedBy
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Local repeat monitoring/records are candidate evidence for identifying the biologically relevant population independently of the development boundary."
  true

connectivityCrossPollinatesS13 : Ibrahim.DashiFirstLinkEdge
connectivityCrossPollinatesS13 = Ibrahim.dashi-first-link-edge
  connectivityMethodNode s13KnowledgeNode Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Landscape/connectivity science informs the counterfactual and validation design, but does not itself prove s 13 essentiality."
  true

populationSupportsS102 : Ibrahim.DashiFirstLinkEdge
populationSupportsS102 = Ibrahim.dashi-first-link-edge
  populationEvidenceNode s102KnowledgeNode Ibrahim.supportedBy
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Independent current/local population records can strengthen exposure and likely-effect analysis under s 102."
  true

------------------------------------------------------------------------
-- Direct intersection with existing legal atom machinery.
------------------------------------------------------------------------

record LegalAtomSourceJoin : Set where
  constructor legal-atom-source-join
  field
    sourceLabel : String
    consumer : Atom.LegalExecutionConsumer
    atom : Atom.LegalExecutionAtom
    admissibleAsInput : Bool
    atomPaidByCurrentPublicSource : Bool
    joinMeaning : String
    firstResidual : String

open LegalAtomSourceJoin public

biolinkS13Join : LegalAtomSourceJoin
biolinkS13Join = legal-atom-source-join
  "Biolink Ipswich longitudinal monitoring series"
  Atom.nca13EssentialityConsumer
  Atom.habitatPopulationEssentialityAtom
  true
  false
  "The series is highly relevant to identifying the relevant population and temporal activity/distribution context, but the public project pages do not themselves prove Springview habitat essentiality."
  "Acquire report bodies/site identities/data; identify the relevant population independently; then calculate the without-site/severance counterfactual."

ikpsS13Join : LegalAtomSourceJoin
ikpsS13Join = legal-atom-source-join
  "IKPS local records/mapping"
  Atom.nca13EssentialityConsumer
  Atom.habitatPopulationEssentialityAtom
  true
  false
  "An independent local observational stream can corroborate or challenge population geography and movement/mortality patterns."
  "Acquire exact dated event records and event types for the relevant landscape; organisation-level statement that records exist does not pay the atom."

biolinkS102Join : LegalAtomSourceJoin
biolinkS102Join = legal-atom-source-join
  "Biolink Ipswich longitudinal monitoring series"
  Atom.nca102InterimOrderConsumer
  Atom.affectedWildlifeHabitatAtom
  true
  false
  "Local monitoring can independently strengthen which threatened wildlife/population is exposed to the approved process."
  "Need site-level spatial/temporal data or an expert opinion applying current evidence to the approved 9281 process."

connectivityS102Join : LegalAtomSourceJoin
connectivityS102Join = legal-atom-source-join
  "McAlpine 2006 + Brunton 2026 connectivity science"
  Atom.nca102InterimOrderConsumer
  Atom.likelySignificantDetrimentalEffectAtom
  true
  false
  "Peer-reviewed connectivity science supports the mechanism and the evidentiary design, especially the need to distinguish structural/potential from realised functional connectivity."
  "A current same-object ecological opinion is still required; general science cannot be promoted into likely significant detrimental effect for Woogaroo."

------------------------------------------------------------------------
-- Dependency-accounting consequence.
------------------------------------------------------------------------

record AcquisitionPriority : Set where
  constructor acquisition-priority
  field
    rank : Nat
    target : String
    whyIndependent : String
    legalConsumer : String

open AcquisitionPriority public

firstAcquisition : AcquisitionPriority
firstAcquisition = acquisition-priority
  1
  "Biolink 2023 and 2025 report bodies/site-level outputs, plus the 2020 baseline report/data if accessible"
  "Independent local longitudinal monitoring rather than another SHG-derived proposition."
  "s 13 viable-population identity first; also s 102 exposure/current-effect context"

secondAcquisition : AcquisitionPriority
secondAcquisition = acquisition-priority
  2
  "IKPS dated rescue/sighting/release records and mapping for Springview/Brookwater/Opossum-Woogaroo/White Rock-Spring Mountain"
  "Independent community/practitioner observational record lineage with long temporal depth."
  "s 13 population geography and s 102 exposure/urgency"

thirdAcquisition : AcquisitionPriority
thirdAcquisition = acquisition-priority
  3
  "Current independent ecological opinion"
  "Independent expert synthesis applying current local records, approved 9281 process and current statutory wording."
  "s 102 likely significant detrimental effect and s 13 essentiality"

------------------------------------------------------------------------
-- WrongType / source-promotion boundaries.
------------------------------------------------------------------------

data ProjectPageEqualsUnderlyingReport : Set where
data MonitoringSeriesExistsEqualsWoogarooFinding : Set where
data RescueRecordEqualsPopulationEstimate : Set where
data QidEqualsLegalIdentity : Set where
data DeweyEqualsSemanticEdge : Set where
data DOIEqualsScientificTruth : Set where
data GeneralConnectivityScienceEqualsSiteConnectivity : Set where
data StructuralConnectivityEqualsRealisedFunctionalConnectivity : Set where
data LocalPopulationRecordEqualsS13Essentiality : Set where
data PeerReviewedMechanismEqualsS102Effect : Set where

projectPageDoesNotBecomeReport : ProjectPageEqualsUnderlyingReport → ⊥
projectPageDoesNotBecomeReport ()

seriesExistenceDoesNotCreateSiteFinding : MonitoringSeriesExistsEqualsWoogarooFinding → ⊥
seriesExistenceDoesNotCreateSiteFinding ()

rescueRecordDoesNotBecomePopulationEstimate : RescueRecordEqualsPopulationEstimate → ⊥
rescueRecordDoesNotBecomePopulationEstimate ()

qidDoesNotCreateLegalIdentity : QidEqualsLegalIdentity → ⊥
qidDoesNotCreateLegalIdentity ()

deweyDoesNotCreateSemanticEdge : DeweyEqualsSemanticEdge → ⊥
deweyDoesNotCreateSemanticEdge ()

doiDoesNotCreateScientificTruth : DOIEqualsScientificTruth → ⊥
doiDoesNotCreateScientificTruth ()

generalScienceDoesNotCreateSiteConnectivity : GeneralConnectivityScienceEqualsSiteConnectivity → ⊥
generalScienceDoesNotCreateSiteConnectivity ()

structuralDoesNotBecomeRealisedConnectivity : StructuralConnectivityEqualsRealisedFunctionalConnectivity → ⊥
structuralDoesNotBecomeRealisedConnectivity ()

populationRecordDoesNotCreateEssentiality : LocalPopulationRecordEqualsS13Essentiality → ⊥
populationRecordDoesNotCreateEssentiality ()

peerReviewDoesNotCreateS102Conclusion : PeerReviewedMechanismEqualsS102Effect → ⊥
peerReviewDoesNotCreateS102Conclusion ()

------------------------------------------------------------------------
-- Current dependency state remains consistent with the existing matrix.
------------------------------------------------------------------------

existingS13Dependency : Dependency.ConsumerDependencyState
existingS13Dependency = Dependency.s13DependencyState

existingS102Dependency : Dependency.ConsumerDependencyState
existingS102Dependency = Dependency.s102DependencyState
