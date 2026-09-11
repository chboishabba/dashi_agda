module DASHI.Law.SensibLawWoogarooExistingLocalKoalaMonitoringSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Canonical
import DASHI.Law.SensibLawWoogarooIbrahimPopulationSourceExtensionExact as Regional
import DASHI.Law.SensibLawWoogarooKoalaScienceSnowballExact as Science
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
  bibliographicIdentityOnly : RetrievalState
  publicSummaryOnly : RetrievalState
  custodianKnownDataNotAcquired : RetrievalState
  exactDatasetOpen : RetrievalState

koalaQid : Id.ItemId
koalaQid = Id.itemId "Q36101"

cityOfIpswichQid : Id.ItemId
cityOfIpswichQid = Id.itemId "Q1631867"

springfieldQid : Id.ItemId
springfieldQid = Id.itemId "Q1838932"

ecologicalConnectivityQid : Id.ItemId
ecologicalConnectivityQid = Id.itemId "Q2993449"

landscapeEcologyQid : Id.ItemId
landscapeEcologyQid = Id.itemId "Q738011"

conservationBiologyQid : Id.ItemId
conservationBiologyQid = Id.itemId "Q641498"

koalaDewey : String
koalaDewey = "599.25"

ecologyDewey : String
ecologyDewey = "577"

conservationDewey : String
conservationDewey = "333.95"

------------------------------------------------------------------------
-- Attributed monitoring/custodian sources.
------------------------------------------------------------------------

ipswichBiodiversity2016 : Source.AttributedSource
ipswichBiodiversity2016 = Source.mkNoDOISource
  "Teresa J. Eyre; Dan Ferguson; Annie L. Kelly; Jian Wang; M. Venz"
  "Ipswich City Council Biodiversity Monitoring Project — Final Report"
  "Queensland Herbarium, Department of Science, Information Technology and Innovation"
  "2016"
  "https://www.researchgate.net/publication/326494130_Ipswich_City_Council_Biodiversity_Monitoring_Project_Final_Report"
  (Source.namedSourceKind "government technical monitoring report")
  "Bibliographic/source identity of the Queensland Herbarium report and its Ipswich monitoring role are retained. A direct authoritative-host report copy has not been acquired in the present Snowball, so detailed White Rock/Spring Mountain findings must not be promoted from secondary citations alone."
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
  "Biolink Ecological Consultants Pty Ltd"
  "Ipswich baseline koala survey"
  "Biolink project description for Ipswich City Council"
  "2020"
  "https://biolink.com.au/ipswich-baseline-koala-survey/"
  (Source.namedSourceKind "consultant project description")
  "Primary producer description confirming an Ipswich Council baseline Koala program covering Mount Grandchester, Flinders-Goolman and White Rock-Spring Mountain, with review of historical records and 63 SAT/Rapid-SAT sites intended to quantify occupancy and metapopulation configuration. It proves program scope/existence, not unpublished site-level results."
  Source.publicAttribution

biolink2025 : Source.AttributedSource
biolink2025 = Source.mkNoDOISource
  "Biolink Ecological Consultants Pty Ltd"
  "Ipswich Biennial koala survey and Population Change Analysis"
  "Biolink project description for Ipswich City Council"
  "2025"
  "https://biolink.com.au/ipswich-biennial-koala-survey-and-population-change-analysis/"
  (Source.namedSourceKind "consultant project description")
  "Primary producer description confirming a third Ipswich monitoring round after 2020 and 2023, using 83 permanent Council-estate sites plus 10 privately owned conservation-agreement properties and integrating field surveys with sighting records to assess activity/distribution change. Used as a direct acquisition lead, not as a substitute for the underlying report/data."
  Source.publicAttribution

ipswichKoalaProtectionSociety : Source.AttributedSource
ipswichKoalaProtectionSociety = Source.mkNoDOISource
  "Ipswich Koala Protection Society Inc."
  "About IKPS — rescue, statistics and mapping records"
  "Ipswich Koala Protection Society public organisation description"
  "2026"
  "https://www.ikps.org.au/about.htm"
  (Source.namedSourceKind "community wildlife rescue data custodian")
  "Primary organisational source: IKPS states that it maintains extensive local Koala records, statistics and habitat/population mapping and rescues more than 180 Koalas per year. Used to route a request for locality-appropriate rescue, mortality, sighting and release records; the organisation statement itself is not occurrence evidence for Springview."
  Source.publicAttribution

localMonitoringAtlas : Source.AttributedSourceAtlas
localMonitoringAtlas = Source.mkSourceAtlas
  "Woogaroo existing local Koala monitoring Snowball"
  "DASHI.Law.SensibLawWoogarooExistingLocalKoalaMonitoringSnowballExact"
  (ipswichBiodiversity2016 ∷ whiteRockMonitoring2021 ∷ biolink2020 ∷ biolink2025 ∷ ipswichKoalaProtectionSociety ∷ [])
  "Independent local monitoring/custodian surfaces. Primary reports, producer project summaries, bibliographic identities and record-custodian statements are kept distinct. Program existence does not import unseen results; adjacent White Rock evidence does not become Springview same-object evidence."

------------------------------------------------------------------------
-- Ibrahim coordinates and legal-atom joins.
------------------------------------------------------------------------

ipswichMonitoringCoordinate : Ibrahim.DashiKnowledgeCoordinate
ipswichMonitoringCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooExistingLocalKoalaMonitoringSnowballExact.agda"
  "Ipswich longitudinal Koala monitoring / population-change program"
  koalaDewey
  (Id.rawItemId koalaQid)
  "2016 Queensland Herbarium bibliography + Biolink 2020/2023/2025 monitoring lineage"

whiteRockMonitoringCoordinate : Ibrahim.DashiKnowledgeCoordinate
whiteRockMonitoringCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooExistingLocalKoalaMonitoringSnowballExact.agda"
  "White Rock-Spring Mountain observed Koala activity / monitoring"
  ecologyDewey
  (Id.rawItemId ecologicalConnectivityQid)
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
  bibliographicIdentityOnly
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  "Report identity, authorship/institution and its place in the Ipswich monitoring lineage are source-paid."
  "Acquire the actual report body from Council/Queensland Herbarium or another authoritative/complete copy before relying on detailed White Rock-Spring Mountain site findings."
  "medium: historical anchor; do not let a secondary citation substitute for the primary report body"

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
  "The existence and scope of the 2025 third-round program are paid: 83 permanent sites, 10 private conservation-agreement properties, repeat 2020/2023/2025 monitoring and population-change analysis."
  "The actual 2023/2025 reports/data, site coordinates/IDs, White Rock-Spring Mountain results, occupancy/activity trends and any population/metapopulation interpretation."
  "HIGHEST: request the underlying 2020, 2023 and 2025 reports/data before commissioning wholly new population fieldwork"

ikpsAcquisition : MonitoringAcquisition
ikpsAcquisition = monitoring-acquisition
  "IKPS rescue/statistics/mapping"
  communityRescueRecordCustodian
  custodianKnownDataNotAcquired
  Atom.likelySignificantDetrimentalEffectAtom
  Atom.nca102InterimOrderConsumer
  "A local specialist custodian publicly states that extensive Koala records/statistics/mapping are maintained."
  "Dated de-identified records around Springfield/Woogaroo/Opossum/White Rock, keeping rescue, sighting, mortality and release records distinct."
  "HIGH: request an appropriate spatial/temporal extract or expert summary; do not infer occurrences from the organisation description"

------------------------------------------------------------------------
-- SOTA calibration: why local longitudinal records now outrank more generic
-- connectivity papers in the acquisition queue.
------------------------------------------------------------------------

sotaConnectivitySource : Source.AttributedSource
sotaConnectivitySource = Science.source Science.bruntonConnectivityReview

record MonitoringSotaCalibration : Set where
  constructor monitoring-sota-calibration
  field
    localPopulationInputPreferred : Bool
    fieldValidationPreferred : Bool
    structuralMapNotRealisedConnectivity : Bool
    existingLocalSeriesFirst : Bool
    thermalSurveyFallback : Bool
    rationale : String

currentMonitoringSotaCalibration : MonitoringSotaCalibration
currentMonitoringSotaCalibration = monitoring-sota-calibration
  true true true true true
  "Brunton et al. 2026 reports that fewer than one quarter of reviewed koala connectivity studies used local-population data, only 30% directly validated outputs with field surveys, and none of the reviewed studies through 2024 mapped realised functional connectivity. Woogaroo therefore prioritises existing Ipswich longitudinal/local records before new generic desktop connectivity modelling; Regional.ellisThermal2026 remains a fallback if a consumer-critical local detection uncertainty survives."

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
  "Request the existing Ipswich/Biolink 2020, 2023 and 2025 Koala monitoring reports/data (especially White Rock-Spring Mountain site IDs/results and population-change analysis) and a locality-appropriate IKPS rescue/sighting/mortality/release mapping extract. Join those carriers to Springview/Opossum/Woogaroo only by explicit spatial/temporal identity. Then give the joined evidence to the independent ecologist for the s 13 population/functional-connectivity analysis and s 102 likely-effect opinion."

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data ProjectSummaryEqualsUnderlyingMonitoringData : Set where
data BibliographicIdentityEqualsReportContents : Set where
data WhiteRockDetectionEqualsSpringviewOccurrence : Set where
data MonitoringProgramEqualsViablePopulationIdentity : Set where
data RescueCustodianEqualsRescueOccurrence : Set where
data AdjacentProjectEqualsSameObject : Set where
data LongitudinalMonitoringEqualsS13Essentiality : Set where
data ProgramCountEqualsIndependentEvidenceCount : Set where
data StructuralConnectivityEqualsRealisedFunctionalConnectivity : Set where

summaryDoesNotCreateData : ProjectSummaryEqualsUnderlyingMonitoringData → ⊥
summaryDoesNotCreateData ()

bibliographyDoesNotCreateReportContents : BibliographicIdentityEqualsReportContents → ⊥
bibliographyDoesNotCreateReportContents ()

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

structuralMapDoesNotBecomeRealisedConnectivity : StructuralConnectivityEqualsRealisedFunctionalConnectivity → ⊥
structuralMapDoesNotBecomeRealisedConnectivity ()

------------------------------------------------------------------------
-- Existing acquisition leaves remain authoritative.
------------------------------------------------------------------------

populationLeaf : Acquisition.AcquisitionLeafReceipt
populationLeaf = Acquisition.s13PopulationLeaf

functionalConnectivityLeaf : Acquisition.AcquisitionLeafReceipt
functionalConnectivityLeaf = Acquisition.functionalConnectivityLeaf

movementRiskLeaf : Acquisition.AcquisitionLeafReceipt
movementRiskLeaf = Acquisition.movementRiskLeaf
