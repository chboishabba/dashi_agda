module DASHI.Law.SensibLawWoogarooExistingLocalKoalaMonitoringSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Canonical
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom
import DASHI.Law.SensibLawWoogarooLocalKoalaPopulationNexusSnowballExact as Local
import DASHI.Law.SensibLawWoogarooPopulationConnectivityAcquisitionExact as Acquisition

------------------------------------------------------------------------
-- EXISTING LOCAL KOALA MONITORING SNOWBALL
--
-- Highest-alpha correction: before commissioning entirely new population work,
-- acquire the existing Ipswich/White Rock longitudinal monitoring and rescue
-- datasets that are already known to exist. Project pages prove program/data
-- existence and scope; they do not silently promote unpublished results.
------------------------------------------------------------------------

data MonitoringCarrierRole : Set where
  primaryGovernmentMonitoringReport : MonitoringCarrierRole
  primaryAdjacentProjectMonitoringReport : MonitoringCarrierRole
  producerProgramDescription : MonitoringCarrierRole
  communityRescueRecordCustodian : MonitoringCarrierRole

data RetrievalState : Set where
  publicReportRead : RetrievalState
  publicSummaryOnly : RetrievalState
  custodianKnownDataNotAcquired : RetrievalState
  exactDatasetOpen : RetrievalState

koalaQid : Id.ItemId
koalaQid = Id.itemId "Q36101"

cityOfIpswichQid : Id.ItemId
cityOfIpswichQid = Id.itemId "Q1631867"

koalaDewey : String
koalaDewey = "599.25"

conservationDewey : String
conservationDewey = "333.9516"

------------------------------------------------------------------------
-- Attributed monitoring/custodian sources.
------------------------------------------------------------------------

ipswichBiodiversity2016 : Source.AttributedSource
ipswichBiodiversity2016 = Source.mkNoDOISource
  "Teresa J. Eyre; Dan Ferguson; Annie L. Kelly; Jian Wang; M. Venz; J. Rowland; M. Mathieson"
  "Ipswich City Council Biodiversity Monitoring Project — Final Report"
  "Queensland Herbarium, Department of Science, Information Technology and Innovation"
  "2016"
  "https://www.researchgate.net/publication/326494130_Ipswich_City_Council_Biodiversity_Monitoring_Project_Final_Report"
  (Source.namedSourceKind "government technical monitoring report")
  "Primary government monitoring report commissioned for Ipswich City Council. White Rock-Spring Mountain was directly surveyed; the report records Koala detections in Council reserves, including White Rock-Spring Mountain, and establishes repeatable monitoring sites/methods. Used as historical local monitoring evidence, not as current Springview occupancy or population identity."
  Source.publicAttribution

whiteRockMonitoring2021 : Source.AttributedSource
whiteRockMonitoring2021 = Source.mkNoDOISource
  "Bower Ecology Pty Ltd"
  "White Rock Koala Monitoring Report"
  "White Rock 2021 Compliance Reporting, EPBC 2014/7388"
  "2021"
  "https://intrapac.com.au/app/uploads/2022/01/EPBC-2014_7388-Compliance-Report-No.-2-%E2%80%93-2021-incl.-supporting-documentation.pdf"
  (Source.namedSourceKind "consultant monitoring report")
  "Primary adjacent-project monitoring report. It records earlier Ipswich Council Koala scats in White Rock-Spring Mountain, a 2016 Koala sighting/scats, a 2019 baseline and 2021 monitoring/historical records. It is independent of Springview SHG ecology but remains a different project/site surface."
  Source.publicAttribution

biolink2020 : Source.AttributedSource
biolink2020 = Source.mkNoDOISource
  "Biolink Ecological Consultants"
  "Ipswich baseline koala survey"
  "Biolink project description for Ipswich City Council"
  "2020"
  "https://biolink.com.au/ipswich-baseline-koala-survey/"
  (Source.namedSourceKind "consultant project description")
  "Producer description confirming an Ipswich Council baseline Koala program covering White Rock-Spring Mountain and other estates, with historical-record review and 63 SAT/Rapid-SAT survey sites intended to quantify occupancy/metapopulation configuration. It proves program scope/existence, not the unpublished site-level results."
  Source.publicAttribution

biolink2025 : Source.AttributedSource
biolink2025 = Source.mkNoDOISource
  "Biolink Ecological Consultants"
  "Ipswich Biennial koala survey and Population Change Analysis"
  "Biolink project description for Ipswich City Council"
  "2025"
  "https://biolink.com.au/ipswich-biennial-koala-survey-and-population-change-analysis/"
  (Source.namedSourceKind "consultant project description")
  "Producer description confirming a third Ipswich monitoring round after 2020 and 2023, using 83 permanent sites plus 10 private conservation properties and integrating field surveys with sighting records to assess activity/distribution change. Used as a direct acquisition lead for current local monitoring, not as a substitute for the underlying report/data."
  Source.publicAttribution

ipswichKoalaProtectionSociety : Source.AttributedSource
ipswichKoalaProtectionSociety = Source.mkNoDOISource
  "Ipswich Koala Protection Society Inc."
  "About IKPS — rescue, statistics and mapping records"
  "Ipswich Koala Protection Society public organisation description"
  "2026"
  "https://www.ikps.org.au/about.htm"
  (Source.namedSourceKind "community wildlife rescue data custodian")
  "Custodian lead: IKPS states that it maintains extensive local Koala records, statistics and habitat/population mapping and rescues more than 180 Koalas per year. Used to route a request for de-identified/locality-appropriate rescue, mortality and population records; the organisation statement itself is not occurrence evidence for Springview."
  Source.publicAttribution

localMonitoringAtlas : Source.AttributedSourceAtlas
localMonitoringAtlas = Source.mkSourceAtlas
  "Woogaroo existing local Koala monitoring Snowball"
  "DASHI.Law.SensibLawWoogarooExistingLocalKoalaMonitoringSnowballExact"
  (ipswichBiodiversity2016 ∷ whiteRockMonitoring2021 ∷ biolink2020 ∷ biolink2025 ∷ ipswichKoalaProtectionSociety ∷ [])
  "Independent local monitoring/custodian surfaces. Primary reports, producer project summaries and record-custodian statements are kept distinct. Program existence does not import unseen results; adjacent White Rock evidence does not become Springview same-object evidence."

------------------------------------------------------------------------
-- Ibrahim coordinates and legal-atom joins.
------------------------------------------------------------------------

ipswichMonitoringCoordinate : Ibrahim.DashiKnowledgeCoordinate
ipswichMonitoringCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooExistingLocalKoalaMonitoringSnowballExact.agda"
  "Ipswich longitudinal Koala monitoring / population-change program"
  koalaDewey
  (Id.rawItemId koalaQid)
  "2016 Queensland Herbarium + Biolink 2020/2023/2025 monitoring lineage"

whiteRockMonitoringCoordinate : Ibrahim.DashiKnowledgeCoordinate
whiteRockMonitoringCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooExistingLocalKoalaMonitoringSnowballExact.agda"
  "White Rock-Spring Mountain observed Koala activity / monitoring"
  koalaDewey
  (Id.rawItemId koalaQid)
  "Bower Ecology 2021 monitoring plus Council/ELA historical detections"

rescueRecordsCoordinate : Ibrahim.DashiKnowledgeCoordinate
rescueRecordsCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooExistingLocalKoalaMonitoringSnowballExact.agda"
  "Ipswich Koala rescue/mortality/population records acquisition"
  conservationDewey
  (Id.rawItemId cityOfIpswichQid)
  "Ipswich Koala Protection Society record custodian"

monitoringToS13 : Ibrahim.DashiFirstLinkEdge
monitoringToS13 = Ibrahim.dashi-first-link-edge
  ipswichMonitoringCoordinate Canonical.s13EssentialityCoordinate Ibrahim.supportedBy
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Existing longitudinal monitoring is the shortest known route to locally grounded occupancy/metapopulation evidence for the s 13 population-identity inquiry. Underlying data/report acquisition remains required."
  true

whiteRockToS13 : Ibrahim.DashiFirstLinkEdge
whiteRockToS13 = Ibrahim.dashi-first-link-edge
  whiteRockMonitoringCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Adjacent White Rock-Spring Mountain detections and repeated monitoring constrain the nearby population/corridor context but do not identify Springview's exact viable population or prove connectivity across the project boundary."
  true

rescueToS102 : Ibrahim.DashiFirstLinkEdge
rescueToS102 = Ibrahim.dashi-first-link-edge
  rescueRecordsCoordinate Canonical.s102StatutoryCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Local rescue/mortality/road records could independently inform movement-risk and cumulative-effect pathways if exact dated/local records are acquired. Custodian existence alone does not pay those facts."
  true

------------------------------------------------------------------------
-- Consumer-specific acquisition state.
------------------------------------------------------------------------

record MonitoringAcquisition : Set where
  constructor monitoring-acquisition
  field
    label : String
    role : MonitoringCarrierRole
    state : RetrievalState
    atom : Atom.LegalExecutionAtom
    consumer : Atom.LegalExecutionConsumer
    currentlyPaid : String
    stillNeeded : String
    priority : String

open MonitoringAcquisition public

biodiversity2016Acquisition : MonitoringAcquisition
biodiversity2016Acquisition = monitoring-acquisition
  "Queensland Herbarium 2016"
  primaryGovernmentMonitoringReport
  publicReportRead
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  "Historical White Rock-Spring Mountain monitoring and at least one Koala detection are source-paid, together with permanent monitoring-site design."
  "Exact spatial relation of relevant sites/detections to Springview/Opossum and later longitudinal change."
  "context paid; use mainly to anchor the monitoring lineage and older local state"

whiteRock2021Acquisition : MonitoringAcquisition
whiteRock2021Acquisition = monitoring-acquisition
  "White Rock 2021 monitoring"
  primaryAdjacentProjectMonitoringReport
  publicReportRead
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  "Adjacent-project historical and repeated Koala detections/scats plus mapped monitoring context are available."
  "Same-object relation to the Springview/Woogaroo population network and any usable coordinates/temporal trend relevant to the corridor question."
  "high supporting value; preserve as independent adjacent monitoring, not Springview evidence"

biolink2025Acquisition : MonitoringAcquisition
biolink2025Acquisition = monitoring-acquisition
  "Ipswich 2025 population-change monitoring"
  producerProgramDescription
  publicSummaryOnly
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  "The existence and scope of the 2025 third-round program are paid: 83 permanent sites, 10 private conservation properties, repeat 2020/2023/2025 monitoring and population-change analysis."
  "The actual report/data, site coordinates/IDs, White Rock-Spring Mountain results, occupancy/activity trends and any population/metapopulation interpretation."
  "HIGHEST: request the underlying 2020, 2023 and 2025 reports/data before commissioning wholly new population fieldwork"

ikpsAcquisition : MonitoringAcquisition
ikpsAcquisition = monitoring-acquisition
  "IKPS rescue/statistics/mapping"
  communityRescueRecordCustodian
  custodianKnownDataNotAcquired
  Atom.likelySignificantDetrimentalEffectAtom
  Atom.nca102InterimOrderConsumer
  "A local specialist custodian publicly states that extensive Koala records/statistics/mapping are maintained."
  "Dated de-identified records around Springfield/Woogaroo/Opossum/White Rock, especially rescue, mortality, movement/road-strike and repeated-location patterns."
  "HIGH: request an appropriate spatial/temporal extract or expert summary; do not infer occurrences from the organisation description"

------------------------------------------------------------------------
-- Highest-alpha correction to acquisition ordering.
------------------------------------------------------------------------

record ExistingMonitoringFrontier : Set where
  constructor existing-monitoring-frontier
  field
    localMonitoringProgramExists : Bool
    repeated2020_2023_2025ProgramExists : Bool
    whiteRockIncludedInMonitoringLineage : Bool
    primaryAdjacentDetectionEvidenceExists : Bool
    localRescueRecordCustodianExists : Bool
    underlying2025ResultsAcquired : Bool
    exactSpringviewPopulationJoinPaid : Bool
    realisedOpossumWoogarooConnectivityPaid : Bool
    nextAction : String

currentExistingMonitoringFrontier : ExistingMonitoringFrontier
currentExistingMonitoringFrontier = existing-monitoring-frontier
  true true true true true
  false false false
  "Before paying for a wholly new population survey, request the existing Ipswich/Biolink 2020, 2023 and 2025 Koala monitoring reports/data (especially White Rock-Spring Mountain site IDs/results and population-change analysis) and a locality-appropriate IKPS rescue/mortality mapping extract. Then give those carriers to the independent ecologist for the s 13 population/functional-connectivity analysis and s 102 movement-risk/effect opinion."

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data ProjectSummaryEqualsUnderlyingMonitoringData : Set where
data WhiteRockDetectionEqualsSpringviewOccurrence : Set where
data MonitoringProgramEqualsViablePopulationIdentity : Set where
data RescueCustodianEqualsRescueOccurrence : Set where
data AdjacentProjectEqualsSameObject : Set where
data LongitudinalMonitoringEqualsS13Essentiality : Set where

data ProgramCountEqualsIndependentEvidenceCount : Set where

summaryDoesNotCreateData : ProjectSummaryEqualsUnderlyingMonitoringData → ⊥
summaryDoesNotCreateData ()

whiteRockDoesNotCreateSpringviewOccurrence : WhiteRockDetectionEqualsSpringviewOccurrence → ⊥
whiteRockDoesNotCreateSpringviewOccurrence ()

monitoringDoesNotIdentifyPopulationAutomatically : MonitoringProgramEqualsViablePopulationIdentity → ⊥
monitoringDoesNotIdentifyPopulationAutomatically ()

custodianDoesNotCreateOccurrence : RescueCustodianEqualsRescueOccurrence → ⊥
custodianDoesNotCreateOccurrence ()

adjacentProjectDoesNotBecomeSameObject : AdjacentProjectEqualsSameObject → ⊥
adjacentProjectDoesNotBecomeSameObject ()

monitoringDoesNotCreateEssentiality : LongitudinalMonitoringEqualsS13Essentiality → ⊥
monitoringDoesNotCreateEssentiality ()

programMultiplicityDoesNotCreateIndependence : ProgramCountEqualsIndependentEvidenceCount → ⊥
programMultiplicityDoesNotCreateIndependence ()

------------------------------------------------------------------------
-- Existing acquisition leaves remain authoritative.
------------------------------------------------------------------------

populationLeaf : Acquisition.AcquisitionLeafReceipt
populationLeaf = Acquisition.s13PopulationLeaf

functionalConnectivityLeaf : Acquisition.AcquisitionLeafReceipt
functionalConnectivityLeaf = Acquisition.functionalConnectivityLeaf

movementRiskLeaf : Acquisition.AcquisitionLeafReceipt
movementRiskLeaf = Acquisition.movementRiskLeaf
