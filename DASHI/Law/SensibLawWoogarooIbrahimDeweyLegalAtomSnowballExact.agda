module DASHI.Law.SensibLawWoogarooIbrahimDeweyLegalAtomSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Identifier
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom
import DASHI.Law.SensibLawWoogarooEvidenceDependencyMatrixExact as Dependency

------------------------------------------------------------------------
-- WOOGAROO IBRAHIM / DEWEY / LEGAL-ATOM SNOWBALL
--
-- Purpose: make acquisition coordinates first-class without letting them
-- silently become legal or ecological conclusions.  A source can have a DOI,
-- QID, Dewey coordinate, canonical link and primary-source role while still
-- leaving the consumer-specific legal atom unpaid.
------------------------------------------------------------------------

data SnowballSourceRole : Set where
  primaryStatute : SnowballSourceRole
  primaryGovernmentDataset : SnowballSourceRole
  primaryGovernmentPlanningEcology : SnowballSourceRole
  primaryProjectComplianceMonitoring : SnowballSourceRole
  primaryGovernmentComplianceAudit : SnowballSourceRole
  practitionerLongitudinalMonitoring : SnowballSourceRole
  peerReviewedMethod : SnowballSourceRole
  peerReviewedLandscapeEcology : SnowballSourceRole

data DeweyRole : Set where
  zoologyMammals : DeweyRole
  biologicalResourcesConservation : DeweyRole
  environmentalLaw : DeweyRole
  localGovernmentPlanning : DeweyRole
  ecologicalMethods : DeweyRole

record SnowballCoordinate : Set where
  constructor snowball-coordinate
  field
    label : String
    source : Source.AttributedSource
    role : SnowballSourceRole
    qid : Identifier.ItemId
    qidMeaning : String
    dewey : String
    deweyRole : DeweyRole
    primaryLink : String
    exactProjectRelation : String
    independentProducer : Bool
    legalAtomUse : String
    acquisitionResidual : String

open SnowballCoordinate public

------------------------------------------------------------------------
-- Canonical semantic coordinates. QIDs are navigation/entity coordinates,
-- not legal or ecological proof.
------------------------------------------------------------------------

koalaQid : Identifier.ItemId
koalaQid = Identifier.itemId "Q36101"

springfieldQid : Identifier.ItemId
springfieldQid = Identifier.itemId "Q1838932"

brookwaterQid : Identifier.ItemId
brookwaterQid = Identifier.itemId "Q4975216"

ipswichCityQid : Identifier.ItemId
ipswichCityQid = Identifier.itemId "Q1631867"

------------------------------------------------------------------------
-- Sources on the current Pareto frontier.
------------------------------------------------------------------------

wildNetKoalaSource : Source.AttributedSource
wildNetKoalaSource = Source.mkNoDOISource
  "Queensland Government — Environment, Tourism, Science and Innovation"
  "WildNet Koala Locations"
  "Queensland Government Open Data / WildNet"
  "2026"
  "https://www.data.qld.gov.au/dataset/wildnet-koala-locations"
  Source.governmentSource
  "Primary government occurrence-record dataset for publicly releasable Koala records. Used to identify candidate local records and their metadata; record count is not population size and a public coordinate may be generalised."
  Source.publicAttribution

wildNetKoalaCoordinate : SnowballCoordinate
wildNetKoalaCoordinate = snowball-coordinate
  "WildNet Koala Locations"
  wildNetKoalaSource
  primaryGovernmentDataset
  koalaQid
  "Koala / Phascolarctos cinereus"
  "599.25"
  zoologyMammals
  "https://www.data.qld.gov.au/dataset/wildnet-koala-locations"
  "Independent government occurrence-data stream; not produced by Saunders Havill Group and not identical to EPBC 2019/8575 project ecology."
  true
  "Candidate input to current threatened-wildlife exposure, local-population identification and s 13/s 102 spatial context."
  "Extract the local sighting-level rows with date, coordinate precision/generalisation, source organisation and observation basis; do not use a gross record count as a population estimate."

biolink2025Source : Source.AttributedSource
biolink2025Source = Source.mkNoDOISource
  "Biolink Ecological Consultants"
  "Ipswich Biennial koala survey and Population Change Analysis"
  "Biolink project page; third Ipswich survey round following 2020 and 2023"
  "2025"
  "https://biolink.com.au/ipswich-biennial-koala-survey-and-population-change-analysis/"
  Source.practitionerSource
  "Longitudinal practitioner monitoring source: 83 permanent Council-managed sites plus 10 private conservation properties in the 2025 round, integrating field results with sightings analysis. Used as an acquisition pointer to the underlying survey/report outputs, not as a substitute for them."
  Source.publicAttribution

biolink2025Coordinate : SnowballCoordinate
biolink2025Coordinate = snowball-coordinate
  "Ipswich 2025 biennial Koala monitoring"
  biolink2025Source
  practitionerLongitudinalMonitoring
  ipswichCityQid
  "City of Ipswich monitoring domain; species coordinate separately Q36101"
  "333.95"
  biologicalResourcesConservation
  "https://biolink.com.au/ipswich-biennial-koala-survey-and-population-change-analysis/"
  "Independent of the Springview development boundary and designed as repeated landscape monitoring; institutional authorship is Biolink, not SHG."
  true
  "High-value input to viable-population identity, temporal trend, occupancy distribution and the without-Springview counterfactual for s 13; current-population context for s 102."
  "Acquire the actual 2020/2023/2025 report/data outputs, especially site identifiers, local White Rock–Spring Mountain/Brookwater/Opossum/Woogaroo results, trend estimates and sighting-data treatment."

biolink2020Source : Source.AttributedSource
biolink2020Source = Source.mkNoDOISource
  "Biolink Ecological Consultants"
  "Ipswich baseline koala survey"
  "Biolink project page"
  "2020"
  "https://biolink.com.au/ipswich-baseline-koala-survey/"
  Source.practitionerSource
  "Baseline Ipswich survey using historical record review plus 63 SAT/Rapid-SAT field sites across Council parks/reserves including White Rock–Spring Mountain. Establishes the starting point for later longitudinal monitoring."
  Source.publicAttribution

biolink2020Coordinate : SnowballCoordinate
biolink2020Coordinate = snowball-coordinate
  "Ipswich 2020 Koala baseline"
  biolink2020Source
  practitionerLongitudinalMonitoring
  ipswichCityQid
  "City of Ipswich monitoring domain; species coordinate separately Q36101"
  "333.95"
  biologicalResourcesConservation
  "https://biolink.com.au/ipswich-baseline-koala-survey/"
  "Independent landscape-monitoring baseline; not same object as 2019/8575 and not generated for Springview approval."
  true
  "Baseline for population configuration and occupancy-change analysis relevant to s 13 essentiality."
  "Recover full baseline report/data and map local survey cells/sites to the Woogaroo/Opossum/Springfield corridor."

firstNineYear6Source : Source.AttributedSource
firstNineYear6Source = Source.mkNoDOISource
  "Saunders Havill Group for Springfield Land Corporation Pty Limited"
  "Annual Compliance Report — EPBC 2016/7676, First Nine Master Planned Residential Development, Year 6"
  "EPBC approval compliance monitoring"
  "2024"
  "https://greaterspringfield.com.au/wp-content/uploads/2024/06/7399-First-Nine-EPBC-ACR-6-062024.pdf"
  Source.institutionalSource
  "Primary adjacent-project compliance/monitoring carrier. It records a 47.25 ha project area, 46.2 ha Koala MNES habitat permitted for impact, and repeat monitoring under a separate EPBC approval. Same consultant family as Springview means institutional independence is false even though observations are a different project/time series."
  Source.publicAttribution

firstNineYear6Coordinate : SnowballCoordinate
firstNineYear6Coordinate = snowball-coordinate
  "EPBC 2016/7676 First Nine Year 6 monitoring"
  firstNineYear6Source
  primaryProjectComplianceMonitoring
  brookwaterQid
  "Brookwater, Queensland; Koala coordinate Q36101"
  "599.25"
  zoologyMammals
  "https://greaterspringfield.com.au/wp-content/uploads/2024/06/7399-First-Nine-EPBC-ACR-6-062024.pdf"
  "Adjacent Brookwater project about 1 km north of Springfield Central; different EPBC action and monitoring observations, but produced by SHG for another Springfield-group entity."
  false
  "Local longitudinal ecological context for realised Koala use/connectivity; useful to stress-test claims that the broader urbanised landscape is functionally unused. Not direct proof about 2019/8575."
  "Extract sighting/SAT locations, survey dates, offset-parcel identities and any high-use locations near Woogaroo Creek; preserve exact project boundary so adjacent observations are not promoted into Springview observations."

firstNineAuditSource : Source.AttributedSource
firstNineAuditSource = Source.mkNoDOISource
  "Department of Climate Change, Energy, the Environment and Water / National EPA"
  "Audit program — EPBC Act approvals: EPBC 2016/7676 First Nine Master Planned Residential Development"
  "Commonwealth compliance-audit summary"
  "2025"
  "https://www.dcceew.gov.au/environment/epbc/compliance/audits"
  Source.governmentSource
  "Primary Commonwealth compliance-history source recording 7 compliant and 2 non-compliant conditions for EPBC 2016/7676. The summary does not identify which two conditions, and it is not evidence of non-compliance for EPBC 2019/8575."
  Source.publicAttribution

firstNineAuditCoordinate : SnowballCoordinate
firstNineAuditCoordinate = snowball-coordinate
  "First Nine Commonwealth compliance audit"
  firstNineAuditSource
  primaryGovernmentComplianceAudit
  brookwaterQid
  "Brookwater adjacent-project compliance object"
  "344.046"
  environmentalLaw
  "https://www.dcceew.gov.au/environment/epbc/compliance/audits"
  "Independent government compliance producer for a different EPBC approval."
  true
  "Compliance-history acquisition lead only; may inform records-request design and monitoring expectations, not the merits or compliance status of 2019/8575."
  "Acquire the detailed audit report/condition findings for 2016/7676 and identify the two non-compliant conditions before drawing any lesson from the adjacent project."

ipswichWoogarooCatchmentSource : Source.AttributedSource
ipswichWoogarooCatchmentSource = Source.mkNoDOISource
  "Ipswich City Council"
  "Brisbane River Catchment — Woogaroo Creek (including Mountain and Opossum creeks)"
  "Ipswich City Council waterways/catchments information"
  "2026"
  "https://www.ipswich.qld.gov.au/About-Council/Initiatives/Environment/Waterways/Catchments-and-Plans/Brisbane-River-Catchment"
  Source.governmentSource
  "Primary local-government landscape source describing Woogaroo Creek and tributaries, significant upper-catchment bushland, importance for securing urban Koala populations, and membership of the Flinders–Karawatha regional corridor."
  Source.publicAttribution

ipswichWoogarooCatchmentCoordinate : SnowballCoordinate
ipswichWoogarooCatchmentCoordinate = snowball-coordinate
  "Woogaroo Creek Council landscape context"
  ipswichWoogarooCatchmentSource
  primaryGovernmentPlanningEcology
  ipswichCityQid
  "City of Ipswich landscape authority; Springfield Q1838932 is a separate place coordinate"
  "333.95"
  biologicalResourcesConservation
  "https://www.ipswich.qld.gov.au/About-Council/Initiatives/Environment/Waterways/Catchments-and-Plans/Brisbane-River-Catchment"
  "Independent local-government landscape description, not SHG project ecology."
  true
  "Supports the population/corridor context for s 13 and the causal exposure context for s 102; does not establish realised movement through the Springview parcel."
  "Join the Council corridor/waterway objects to Biolink/WildNet monitoring and the exact Springview/Opossum geometry."

satMethodSource : Source.AttributedSource
satMethodSource = Source.mkDOISource
  "Stephen Phillips; John Callaghan"
  "The Spot Assessment Technique: a tool for determining localised levels of habitat use by Koalas Phascolarctos cinereus"
  "Australian Zoologist 35(3)"
  "2011"
  "10.7882/AZ.2011.029"
  "https://doi.org/10.7882/AZ.2011.029"
  Source.academicArticleSource
  "Peer-reviewed method lineage for SAT/Rapid-SAT habitat-use evidence used in Koala monitoring. Method validity does not automatically validate any particular site's execution, sampling design or legal inference."
  Source.publicAttribution

satMethodCoordinate : SnowballCoordinate
satMethodCoordinate = snowball-coordinate
  "SAT method lineage"
  satMethodSource
  peerReviewedMethod
  koalaQid
  "Koala / Phascolarctos cinereus"
  "590.72"
  ecologicalMethods
  "https://doi.org/10.7882/AZ.2011.029"
  "General method source; not a Woogaroo observation carrier."
  true
  "Methodological support for interpreting Biolink/First Nine SAT-based evidence."
  "For any local monitoring claim, preserve survey design, site selection, repeatability and sampling date rather than treating citation to the SAT paper as payment of the local observation."

mappingScaleSource : Source.AttributedSource
mappingScaleSource = Source.mkDOISource
  "Daniel L. Mitchell; Mariela Soto-Berelov; William T. Langford; Simon D. Jones"
  "Factors confounding koala habitat mapping at multiple decision-making scales"
  "Ecological Management & Restoration 22"
  "2021"
  "10.1111/emr.12468"
  "https://doi.org/10.1111/emr.12468"
  Source.academicArticleSource
  "Peer-reviewed warning that Koala habitat mapping is scale/method dependent. Used as a calibration boundary between regional habitat maps, local field observations and legal consumers."
  Source.publicAttribution

mappingScaleCoordinate : SnowballCoordinate
mappingScaleCoordinate = snowball-coordinate
  "Koala habitat mapping scale/confounding"
  mappingScaleSource
  peerReviewedLandscapeEcology
  koalaQid
  "Koala / Phascolarctos cinereus"
  "333.95"
  biologicalResourcesConservation
  "https://doi.org/10.1111/emr.12468"
  "General scientific calibration source; not same object as Springview."
  true
  "Supports the firewall that regional mapping, project habitat scoring, occurrence points and population identity answer different questions."
  "Use to design the expert-input request and GIS evidence hierarchy; do not promote a general mapping-method paper into a parcel-specific conclusion."

------------------------------------------------------------------------
-- Legal-atom / Ibrahim routing. Acquisition can snowball broadly, but payment
-- is consumer ordered.
------------------------------------------------------------------------

data SnowballLegalEdge : Set where
  supportedBy
  dependsOn
  generalisesTo
  crossPollinatesWith
  sameObjectNeeded : SnowballLegalEdge

record AtomSnowballRoute : Set where
  constructor atom-snowball-route
  field
    sourceCoordinate : SnowballCoordinate
    edge : SnowballLegalEdge
    consumer : String
    targetAtom : String
    sourcePaid : Bool
    consumerPaid : Bool
    firstResidual : String

open AtomSnowballRoute public

wildNetToS13Population : AtomSnowballRoute
wildNetToS13Population = atom-snowball-route
  wildNetKoalaCoordinate
  supportedBy
  "NCA s 13 essentiality"
  "viable local Koala population identity / distribution"
  true false
  "Sightings must be converted into a defensible population/distribution object with precision, date and survey-effort controls; observations alone do not identify a viable population."

biolinkToS13Population : AtomSnowballRoute
biolinkToS13Population = atom-snowball-route
  biolink2025Coordinate
  dependsOn
  "NCA s 13 essentiality"
  "viable population identity and longitudinal occupancy trend"
  true false
  "Acquire the underlying Ipswich monitoring outputs/data and isolate the White Rock–Spring Mountain / Brookwater / Woogaroo-Opossum subgraph before paying the population-to-site essentiality join."

firstNineToConnectivity : AtomSnowballRoute
firstNineToConnectivity = atom-snowball-route
  firstNineYear6Coordinate
  crossPollinatesWith
  "NCA s 13 and s 102"
  "realised local Koala use / connectivity context"
  true false
  "Different project and same consultant family: exact monitoring locations can support adjacent-landscape use, but cannot be rewritten as Springview occurrence or independent SHG replication."

councilToLandscapePopulation : AtomSnowballRoute
councilToLandscapePopulation = atom-snowball-route
  ipswichWoogarooCatchmentCoordinate
  supportedBy
  "NCA s 13 and s 102"
  "regional corridor / urban-Koala-population context"
  true false
  "Join government landscape context to sighting/monitoring evidence and the exact project process; corridor designation alone does not pay viable-population identity or likely significant detrimental effect."

satToMonitoringMethod : AtomSnowballRoute
satToMonitoringMethod = atom-snowball-route
  satMethodCoordinate
  generalisesTo
  "evidence-quality consumer"
  "SAT/Rapid-SAT method validity"
  true true
  "Local survey execution and sampling adequacy remain source-specific even when the general method is peer reviewed."

mappingScaleToGISBoundary : AtomSnowballRoute
mappingScaleToGISBoundary = atom-snowball-route
  mappingScaleCoordinate
  crossPollinatesWith
  "s 13 / s 102 spatial evidence"
  "map-scale and representation adequacy"
  true true
  "No regional/state habitat map is promoted into parcel-level essentiality or significant-effect without the same-object ecological bridge."

------------------------------------------------------------------------
-- Current Pareto order after quotienting source dependencies.
------------------------------------------------------------------------

record IbrahimParetoFrontier : Set where
  constructor ibrahim-pareto-frontier
  field
    first : String
    second : String
    third : String
    fourth : String
    genericLiteratureLowerPriority : Bool
    sourceDependencyQuotientRequired : Bool

currentIbrahimParetoFrontier : IbrahimParetoFrontier
currentIbrahimParetoFrontier = ibrahim-pareto-frontier
  "WildNet: extract local sighting-level Koala records with metadata/precision rather than aggregate counts."
  "Biolink 2020/2023/2025: acquire the underlying longitudinal monitoring outputs and isolate the local White Rock–Spring Mountain / Brookwater / Woogaroo-Opossum population signal."
  "First Nine 2016/7676: extract repeat monitoring locations/results and the detailed 2025 compliance-audit findings, preserving different-project/same-consultant boundaries."
  "Join the independent monitoring/government landscape evidence to Springview habitat function, then commission the current expert opinion for s 13 population essentiality and s 102 likely significant detrimental effect."
  true
  true

------------------------------------------------------------------------
-- Canonical dependency owner remains authoritative.
------------------------------------------------------------------------

s102Dependency : Dependency.ConsumerDependencyState
s102Dependency = Dependency.s102DependencyState

s13Dependency : Dependency.ConsumerDependencyState
s13Dependency = Dependency.s13DependencyState

------------------------------------------------------------------------
-- No-promotion / WrongType boundaries.
------------------------------------------------------------------------

data QidEqualsLegalFact : Set where
data DeweyEqualsLegalAuthority : Set where
data DOIEqualsSameObjectEvidence : Set where
data PrimarySourceEqualsConsumerSatisfied : Set where
data AdjacentProjectEqualsSpringview : Set where
data SameConsultantDifferentProjectEqualsIndependentProducer : Set where
data WildNetRecordCountEqualsPopulationSize : Set where
data CorridorDescriptionEqualsRealisedMovement : Set where
data PeerReviewedMethodEqualsLocalSurveyAdequacy : Set where

data MultipleCoordinatesEqualsIndependentEvidence : Set where

qidDoesNotCreateLegalFact : QidEqualsLegalFact → ⊥
qidDoesNotCreateLegalFact ()

deweyDoesNotCreateLegalAuthority : DeweyEqualsLegalAuthority → ⊥
deweyDoesNotCreateLegalAuthority ()

doiDoesNotCreateSameObjectEvidence : DOIEqualsSameObjectEvidence → ⊥
doiDoesNotCreateSameObjectEvidence ()

primaryDoesNotPayConsumer : PrimarySourceEqualsConsumerSatisfied → ⊥
primaryDoesNotPayConsumer ()

adjacentDoesNotBecomeSpringview : AdjacentProjectEqualsSpringview → ⊥
adjacentDoesNotBecomeSpringview ()

sameConsultantDifferentProjectDoesNotCreateIndependentProducer : SameConsultantDifferentProjectEqualsIndependentProducer → ⊥
sameConsultantDifferentProjectDoesNotCreateIndependentProducer ()

wildNetCountDoesNotBecomePopulation : WildNetRecordCountEqualsPopulationSize → ⊥
wildNetCountDoesNotBecomePopulation ()

corridorDescriptionDoesNotBecomeMovement : CorridorDescriptionEqualsRealisedMovement → ⊥
corridorDescriptionDoesNotBecomeMovement ()

methodCitationDoesNotPayLocalSurvey : PeerReviewedMethodEqualsLocalSurveyAdequacy → ⊥
methodCitationDoesNotPayLocalSurvey ()

coordinatesDoNotCreateIndependence : MultipleCoordinatesEqualsIndependentEvidence → ⊥
coordinatesDoNotCreateIndependence ()
