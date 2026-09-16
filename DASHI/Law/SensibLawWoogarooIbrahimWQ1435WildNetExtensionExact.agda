module DASHI.Law.SensibLawWoogarooIbrahimWQ1435WildNetExtensionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Canonical
import DASHI.Law.SensibLawWoogarooExistingLocalKoalaMonitoringSnowballExact as Monitoring
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom

------------------------------------------------------------------------
-- THIN WQ1435 / WILDNET EXTENSION
--
-- Adds an independent Queensland-government biodiversity carrier for the
-- creek system that expressly includes Woogaroo Creek and its tributaries.
-- This extends the existing Ibrahim/Snowball graph; it does not create a new
-- traversal, attribution, legal-atom or evidence-dependency architecture.
------------------------------------------------------------------------

data LocalRecordRelation : Set where
  exactSpringview : LocalRecordRelation
  woogarooCatchmentFamily : LocalRecordRelation
  broaderRegional : LocalRecordRelation

data RetrievalState : Set where
  publicAggregateRead : RetrievalState
  sightingMetadataAvailable : RetrievalState
  exactPointExtractNotAcquired : RetrievalState

koalaQid : Id.ItemId
koalaQid = Id.itemId "Q36101"

wildlifeCorridorQid : Id.ItemId
wildlifeCorridorQid = Id.itemId "Q864912"

ecologicalConnectivityQid : Id.ItemId
ecologicalConnectivityQid = Id.itemId "Q2993449"

koalaDewey : String
koalaDewey = "599.25"

ecologyDewey : String
ecologyDewey = "577"

------------------------------------------------------------------------
-- Attribution: primary government web/data carriers, DOI not applicable.
------------------------------------------------------------------------

wq1435WildlifeSource : Source.AttributedSource
wq1435WildlifeSource = Source.mkNoDOISource
  "Department of the Environment, Tourism, Science and Innovation, Queensland"
  "Wildlife of EPP (Water) scheduled EVs and WQOs plan—Sandy, Six Mile, Wolston, Woogaroo and Goodna Creeks (WQ1435)"
  "WetlandInfo / WildNet-derived wildlife report"
  "2025"
  "https://wetlandinfo.detsi.qld.gov.au/wetlands/facts-maps/wildlife/?AreaID=epp-water-plan-sandy-six-mile-wolston-woogaroo-goodna-creeks-wq1435"
  Source.governmentSource
  "Primary Queensland-government aggregate of filtered WildNet sightings for the WQ1435 plan area. The Koala row reports NCA Endangered, EPBC Endangered, 518 records, 0 specimens and last seen 19 June 2025. The geographic carrier includes Sandy, Six Mile, Wolston, Woogaroo and Goodna Creeks and their scheduled area; WetlandInfo area reports may include sightings up to 1 km outside the area. Used as an independent local/catchment evidence carrier, not as a Springview population count or exact project-site occurrence record."
  Source.publicAttribution

wildNetMetadataSource : Source.AttributedSource
wildNetMetadataSource = Source.mkNoDOISource
  "Department of the Environment, Tourism, Science and Innovation, Queensland"
  "Species sightings — spatial metadata"
  "WetlandInfo metadata for WildNet spatial extract"
  "2026"
  "https://wetlandinfo.detsi.qld.gov.au/wetlands/facts-maps/get-mapping-help/metadata/species/"
  Source.governmentSource
  "Primary metadata for interpreting WetlandInfo sighting statistics: records classed as erroneous or duplicate are excluded; retained records have location precision no worse than 10,000 m and non-zero counts; reports for a specific area include sightings up to 1 km outside that area. Used to constrain what the WQ1435 aggregate can and cannot prove."
  Source.publicAttribution

wildNetPlatformSource : Source.AttributedSource
wildNetPlatformSource = Source.mkNoDOISource
  "Queensland Government"
  "WildNet platform"
  "Queensland Government species-information service"
  "2025"
  "https://www.qld.gov.au/environment/plants-animals/species-information/wildnet"
  Source.governmentSource
  "Primary platform description: WildNet contains wildlife sightings, survey results, species profiles, species-location records and source/project metadata, with data continuously collated and vetted. Used as the acquisition route for exact sighting-level metadata after the aggregate WQ1435 discovery."
  Source.publicAttribution

wq1435WildNetAtlas : Source.AttributedSourceAtlas
wq1435WildNetAtlas = Source.mkSourceAtlas
  "Woogaroo WQ1435 WildNet local-evidence Snowball"
  "DASHI.Law.SensibLawWoogarooIbrahimWQ1435WildNetExtensionExact"
  (wq1435WildlifeSource ∷ wildNetMetadataSource ∷ wildNetPlatformSource ∷ [])
  "Government biodiversity aggregate plus its interpretation metadata and sighting-level acquisition route. DOI is not applicable to these government web/data carriers. QID/Dewey coordinates below are navigation only. The three pages are one government data lineage and are not counted as three independent biological replications."

------------------------------------------------------------------------
-- Exact aggregate receipt. The numeric fields are source statistics, not an
-- estimated population size and not a count of distinct living individuals.
------------------------------------------------------------------------

record WQ1435KoalaAggregate : Set where
  constructor wq1435-koala-aggregate
  field
    areaLabel : String
    scientificName : String
    ncaStatus : String
    epbcStatus : String
    records : String
    specimens : String
    latestIncludedSightingDate : String
    sourceFiltersDuplicatesAndErrors : Bool
    maximumAcceptedLocationPrecisionMetres : String
    areaReportMayIncludeOutsideBufferMetres : String
    distinctIndividualCountKnown : Bool
    exactSpringviewSubsetKnown : Bool

open WQ1435KoalaAggregate public

currentWQ1435KoalaAggregate : WQ1435KoalaAggregate
currentWQ1435KoalaAggregate = wq1435-koala-aggregate
  "Sandy, Six Mile, Wolston, Woogaroo and Goodna Creeks (WQ1435)"
  "Phascolarctos cinereus"
  "Endangered"
  "Endangered"
  "518"
  "0"
  "19 June 2025"
  true
  "10000"
  "1000"
  false
  false

------------------------------------------------------------------------
-- Ibrahim / Dewey / QID coordinate and typed graph edges.
------------------------------------------------------------------------

wq1435KoalaCoordinate : Ibrahim.DashiKnowledgeCoordinate
wq1435KoalaCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimWQ1435WildNetExtensionExact.agda"
  "Queensland WildNet/WetlandInfo WQ1435 Koala sighting aggregate"
  koalaDewey
  (Id.rawItemId koalaQid)
  "primary: DETSI WetlandInfo WQ1435 wildlife report; WildNet taxon 860"

wq1435ToS102 : Ibrahim.DashiFirstLinkEdge
wq1435ToS102 = Ibrahim.dashi-first-link-edge
  wq1435KoalaCoordinate Canonical.s102StatutoryCoordinate Ibrahim.supportedBy
  Ibrahim.canonicalDashiFirstLinkPolicy
  "An independent Queensland-government data lineage records a large body of Koala sightings in the creek-plan area expressly including Woogaroo Creek, with sightings as recent as June 2025. This strengthens current/local biological plausibility and acquisition priority, but the broad area and precision rules prevent promotion to exact Springview exposure or likely significant detrimental effect."
  true

wq1435ToS13 : Ibrahim.DashiFirstLinkEdge
wq1435ToS13 = Ibrahim.dashi-first-link-edge
  wq1435KoalaCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "The WQ1435 aggregate independently shows a substantial recorded Koala presence in the wider creek system containing Woogaroo. It justifies drilling down to sighting/project metadata and local monitoring for population structure; it does not identify the viable population or make Springview habitat essential."
  true

------------------------------------------------------------------------
-- Legal atom intersection.
------------------------------------------------------------------------

record WQ1435AtomBinding : Set where
  constructor wq1435-atom-binding
  field
    atom : Atom.LegalExecutionAtom
    consumer : Atom.LegalExecutionConsumer
    relation : LocalRecordRelation
    sourceIndependentOfSHG : Bool
    admissibleAsInput : Bool
    sameObjectSpringviewPaid : Bool
    atomComplete : Bool
    contribution : String
    residual : String

open WQ1435AtomBinding public

wq1435S102Binding : WQ1435AtomBinding
wq1435S102Binding = wq1435-atom-binding
  Atom.affectedWildlifeHabitatAtom
  Atom.nca102InterimOrderConsumer
  woogarooCatchmentFamily
  true true false false
  "Adds a government biodiversity-data producer independent of SHG: 518 filtered Koala sighting records are reported across the WQ1435 creek-plan area including Woogaroo Creek, with a latest included sighting dated 19 June 2025."
  "Acquire sighting-level metadata/coordinates and determine which records fall in or functionally relate to Woogaroo/Opossum/Springview and the approved 9281 process. Record count alone is not the s 102 effect conclusion."

wq1435S13Binding : WQ1435AtomBinding
wq1435S13Binding = wq1435-atom-binding
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  woogarooCatchmentFamily
  true true false false
  "Moves the population inquiry closer to current local data: Queensland's own biodiversity system records many Koala sightings in the creek-plan area containing Woogaroo."
  "Resolve the spatial/temporal distribution and source projects behind those records; then join them to the Ipswich 2020/2023/2025 monitoring lineage and viable-population/connectivity analysis."

------------------------------------------------------------------------
-- Pareto consequence: drill down before acquiring more generic papers.
------------------------------------------------------------------------

record WQ1435ParetoFrontier : Set where
  constructor wq1435-pareto-frontier
  field
    governmentCatchmentAggregatePaid : Bool
    recentKoalaRecordPaid : Bool
    independentOfSHGEcology : Bool
    sightingLevelWildNetRouteKnown : Bool
    exactWoogarooOpossumSubsetPaid : Bool
    exactSpringviewSubsetPaid : Bool
    viablePopulationIdentityPaid : Bool
    s102EffectPaid : Bool
    nextCut : String

currentWQ1435ParetoFrontier : WQ1435ParetoFrontier
currentWQ1435ParetoFrontier = wq1435-pareto-frontier
  true true true true
  false false false false
  "Highest-alpha next cut: use WildNet sighting-level export/metadata and the existing Ipswich monitoring Snowball to isolate the Woogaroo/Opossum/White Rock-Spring Mountain subset, dates, precision and source projects. Do not collect another generic fragmentation paper unless it supplies a genuinely new mechanism needed by a live consumer."

monitoringFrontier : Monitoring.ExistingMonitoringFrontier
monitoringFrontier = Monitoring.currentExistingMonitoringFrontier

------------------------------------------------------------------------
-- Attribution / WrongType firewalls.
------------------------------------------------------------------------

data RecordsEqualDistinctKoalas : Set where
data WQ1435EqualsSpringview : Set where
data LatestSightingEqualsCurrentOccupationEverywhere : Set where
data GovernmentDatabaseEqualsIndependentPopulationStudy : Set where
data AreaRecordCountEqualsViablePopulation : Set where
data CatchmentOccurrenceEqualsS13Essentiality : Set where
data CatchmentOccurrenceEqualsS102Effect : Set where
data ThreeGovernmentPagesEqualThreeIndependentCarriers : Set where

recordsDoNotBecomeDistinctAnimals : RecordsEqualDistinctKoalas → ⊥
recordsDoNotBecomeDistinctAnimals ()

wq1435DoesNotBecomeSpringview : WQ1435EqualsSpringview → ⊥
wq1435DoesNotBecomeSpringview ()

latestDateDoesNotCreateUbiquitousCurrentOccupation : LatestSightingEqualsCurrentOccupationEverywhere → ⊥
latestDateDoesNotCreateUbiquitousCurrentOccupationEverywhere ()

governmentDatabaseDoesNotBecomePopulationStudy : GovernmentDatabaseEqualsIndependentPopulationStudy → ⊥
governmentDatabaseDoesNotBecomePopulationStudy ()

recordCountDoesNotCreateViablePopulation : AreaRecordCountEqualsViablePopulation → ⊥
recordCountDoesNotCreateViablePopulation ()

catchmentOccurrenceDoesNotCreateEssentiality : CatchmentOccurrenceEqualsS13Essentiality → ⊥
catchmentOccurrenceDoesNotCreateEssentiality ()

catchmentOccurrenceDoesNotCreateS102Effect : CatchmentOccurrenceEqualsS102Effect → ⊥
catchmentOccurrenceDoesNotCreateS102Effect ()

pagesInOneLineageDoNotCreateIndependentReplications : ThreeGovernmentPagesEqualThreeIndependentCarriers → ⊥
pagesInOneLineageDoNotCreateIndependentReplications ()
