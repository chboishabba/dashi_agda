module DASHI.Culture.MissingDeceasedIbrahimAcquisitionTraversalExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.IbrahimEnglishParentCoverageGapAtlasExact as Ibrahim
import DASHI.Wikimedia.IbrahimFirstLinkSourceArchaeologyLedgerExact as IbrahimSource

------------------------------------------------------------------------
-- IBRAHIM-GUIDED SCIENTIST ACQUISITION TRAVERSAL
--
-- Thin navigation owner only. Ibrahim-style graph traversal is used to rank
-- adjacent acquisition surfaces for the missing/deceased-scientist work.
-- Current hand-inspected Wikipedia/Wikidata neighbours remain semantic/search
-- coordinates unless the original Ibrahim parser policy has actually been run.
-- They do NOT create evidence authority, same-object identity, person identity,
-- custody, succession, motive or causation.
--
-- Method attribution:
-- Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's First
-- Link Network", Journal of Computational Science 19 (2017), 21-30.
-- DOI 10.1016/j.jocs.2016.12.001; arXiv:1605.00309.
------------------------------------------------------------------------

data TraversalEdgeClass : Set where
  parserEquivalentCurrentFirstLink
  currentSemanticNeighbour
  wikidataBroaderCoordinate
  historicalIbrahimPaidEdge : TraversalEdgeClass

record ScientistAcquisitionTraversal : Set where
  constructor scientist-acquisition-traversal
  field
    scientistLane : String
    unpaidFrontier : String
    seedConcept : String
    seedQid : String
    nextConcept : String
    nextQid : String
    edgeClass : TraversalEdgeClass
    observationDate : String
    sourceLink : String
    deweyTraversal : String
    acquisitionReading : String
    parserEquivalentExtractionPaid : Bool
    primaryObjectStillRequired : Bool
    graphEdgeCreatesEvidenceAuthority : Bool
    graphEdgeCreatesSameObjectIdentity : Bool

open ScientistAcquisitionTraversal public

------------------------------------------------------------------------
-- Amy: the public POAMS object is a technical report. Current English describes
-- a technical report as a document reporting technical/scientific research.
-- This is a useful semantic neighbourhood for routing toward report-series,
-- research-administration and STI metadata, but no parser-equivalent current
-- first-link edge is asserted here.
------------------------------------------------------------------------

amyTechnicalReportToResearch : ScientistAcquisitionTraversal
amyTechnicalReportToResearch = scientist-acquisition-traversal
  "Amy Eskridge / POAMS"
  "exact MSFC EDAA/NF-1676B + attached STI/manuscript version"
  "technical report"
  "Q3099732"
  "research"
  "Q42240"
  currentSemanticNeighbour
  "2026-09-11"
  "https://en.wikipedia.org/wiki/Technical_report"
  "001 Knowledge / 500 Science traversal; report itself remains NASA Subject Category 70 / Physics"
  "Current article semantics route from technical-report identity toward research/report administration and STI metadata. The conclusion-paying object remains the exact MSFC release-authorisation record."
  false true false false

------------------------------------------------------------------------
-- Maiwald: spectroscopy is currently defined through spectra/electromagnetic
-- radiation and the unresolved scientific leaf is raw/reduced research data.
-- The graph routes topical science toward data/metadata provenance without
-- treating affiliation or publication metadata as data custody.
------------------------------------------------------------------------

maiwaldSpectroscopyToElectromagneticSpectrum : ScientistAcquisitionTraversal
maiwaldSpectroscopyToElectromagneticSpectrum = scientist-acquisition-traversal
  "Frank W. Maiwald / action spectroscopy"
  "raw/reduced ion-action spectra + figure/version/dataset crosswalk"
  "spectroscopy"
  "Q483666"
  "electromagnetic spectrum"
  "Q133139"
  currentSemanticNeighbour
  "2026-09-11"
  "https://en.wikipedia.org/wiki/Spectroscopy"
  "543.5 Spectroscopy / 540 Chemistry"
  "The current semantic neighbourhood confirms the measurement domain but does not identify the data carrier. Snowball next through research-data and metadata repositories, using DOI/deposit identities rather than author-name matching."
  false true false false

maiwaldResearchDataCoordinate : ScientistAcquisitionTraversal
maiwaldResearchDataCoordinate = scientist-acquisition-traversal
  "Frank W. Maiwald / action spectroscopy"
  "raw/reduced ion-action spectra + custody/version identity"
  "research data"
  "Q15809982"
  "data"
  "Q42848"
  wikidataBroaderCoordinate
  "2026-09-11"
  "https://www.wikidata.org/wiki/Q15809982"
  "001.4 Research methods / 540 Chemistry traversal only"
  "Treat raw spectra, reduced spectra, fitted/calculated spectra, coordinates and SI figures as distinct data manifestations. Search DOI-bearing deposits and repository metadata before inferring custody from a publication or affiliation."
  false true false false

------------------------------------------------------------------------
-- Reza: current patent semantics route directly to intellectual property/legal
-- record surfaces. This ranks patent-family, assignment and inventor-identity
-- records above secondary role repetition, while JPL employment remains a
-- separate primary-object leaf. No parser-equivalent current edge is claimed.
------------------------------------------------------------------------

rezaPatentToIntellectualProperty : ScientistAcquisitionTraversal
rezaPatentToIntellectualProperty = scientist-acquisition-traversal
  "Monica Jacinto Reza / materials processing"
  "patent-inventor identity weld + primary JPL event-time role"
  "patent"
  "Q253623"
  "intellectual property"
  "Q131257"
  currentSemanticNeighbour
  "2026-09-11"
  "https://en.wikipedia.org/wiki/Patent"
  "346.048 Intellectual property / 620 Engineering"
  "Follow exact patent-family, inventor-name, assignment and institutional identity records first; keep the independent JPL personnel/org-chart leaf separate from patent identity."
  false true false false

------------------------------------------------------------------------
-- McCasland: distinguish Wikidata's specific company-register item from the
-- broader trade-register item. Current English semantics say a company register
-- records business organisations/companies under a jurisdiction. This ranks the
-- government legal-entity history above biographies and client narratives.
------------------------------------------------------------------------

mccaslandCompanyRegisterToCompany : ScientistAcquisitionTraversal
mccaslandCompanyRegisterToCompany = scientist-acquisition-traversal
  "William Neil McCasland / DBE Consulting"
  "actual New Mexico entity/member-manager/ownership chronology"
  "company register"
  "Q134611895"
  "company"
  "Q783794"
  currentSemanticNeighbour
  "2026-09-11"
  "https://en.wikipedia.org/wiki/Company_register"
  "338.7 Enterprises / 650 Management traversal only"
  "Prioritise the government company-register/entity-history carrier. Current biographies may guide the query but cannot pay founder, owner, manager or event-time corporate status."
  false true false false

mccaslandTradeRegisterCoordinate : ScientistAcquisitionTraversal
mccaslandTradeRegisterCoordinate = scientist-acquisition-traversal
  "William Neil McCasland / DBE Consulting"
  "jurisdictional registry identity for the Albuquerque DBE entity"
  "trade register"
  "Q1394657"
  "company register / business registry"
  "Q134611895"
  wikidataBroaderCoordinate
  "2026-09-11"
  "https://www.wikidata.org/wiki/Q1394657"
  "338.7 Enterprises / 650 Management traversal only"
  "Retain Q1394657 as the broader trade-register coordinate and Q134611895 as the specific company-register coordinate. Neither identifies DBE Consulting LLC without the New Mexico registry object/entity identifier."
  false true false false

------------------------------------------------------------------------
-- Cross-lane metadata funnel. Amy's DAA, Maiwald's CHORUS/NTRS harvest and
-- LeBlanc's freeze/role-state problem all depend on metadata/manifests rather
-- than another topical science paper. Q180160 and Q42848 are traversal/search
-- coordinates only.
------------------------------------------------------------------------

record SharedMetadataFunnel : Set where
  constructor shared-metadata-funnel
  field
    concept : String
    conceptQid : String
    broaderConcept : String
    broaderQid : String
    affectedLanes : String
    deweyCoordinates : String
    graphRanksAdministrativeMetadata : Bool
    metadataItselfPaysUnderlyingObjectIdentity : Bool
    boundedReading : String

open SharedMetadataFunnel public

scientistAdministrativeMetadataFunnel : SharedMetadataFunnel
scientistAdministrativeMetadataFunnel = shared-metadata-funnel
  "metadata"
  "Q180160"
  "information / data"
  "Q11028 / Q42848"
  "Amy EDAA/STI release metadata; Maiwald CHORUS/NTRS/ACS manifestation metadata; LeBlanc role-snapshot/freeze metadata"
  "025.3 / 005.7 metadata coordinates; domain-specific Dewey remains traversal-only"
  true
  false
  "Ibrahim-style funneling ranks metadata/manifestation layers because multiple live frontiers converge there. Metadata can expose identifiers, dates, authorship and routing, but it does not manufacture the underlying manuscript, raw dataset, personnel state or succession relation."

------------------------------------------------------------------------
-- Source and historical-snapshot boundary.
------------------------------------------------------------------------

record IbrahimScientistTraversalBoundary : Set where
  constructor ibrahim-scientist-traversal-boundary
  field
    methodDoiRecorded : Bool
    methodArxivRecorded : Bool
    currentEdgesRevisionSensitive : Bool
    exactNovember2014DumpDayStillUnpaid : Bool
    currentScientistEdgesClaimedAsHistorical2014Edges : Bool
    handInspectionCalledParserEquivalentFirstLink : Bool
    qidUsedAsSearchCoordinateOnly : Bool
    deweyUsedAsTraversalCoordinateOnly : Bool
    firstLinkAdjacencyCreatesProofDependency : Bool
    firstLinkAdjacencyCreatesSourceAuthority : Bool
    firstLinkTraversalMayRankNextAcquisition : Bool

open IbrahimScientistTraversalBoundary public

canonicalIbrahimScientistTraversalBoundary : IbrahimScientistTraversalBoundary
canonicalIbrahimScientistTraversalBoundary = ibrahim-scientist-traversal-boundary
  true true true true false false true true false false true
