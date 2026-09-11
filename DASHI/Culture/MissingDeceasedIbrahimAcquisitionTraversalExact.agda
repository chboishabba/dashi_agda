module DASHI.Culture.MissingDeceasedIbrahimAcquisitionTraversalExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.IbrahimEnglishParentCoverageGapAtlasExact as Ibrahim
import DASHI.Wikimedia.IbrahimFirstLinkSourceArchaeologyLedgerExact as IbrahimSource

------------------------------------------------------------------------
-- IBRAHIM-GUIDED SCIENTIST ACQUISITION TRAVERSAL
--
-- Thin navigation owner only.  Ibrahim-style first-link traversal is used to
-- rank adjacent acquisition surfaces for the missing/deceased-scientist work.
-- It does NOT create evidence authority, same-object identity, person identity,
-- custody, succession, motive or causation.  Those remain owned by the source-
-- specific scientific/evidence modules.
--
-- Method attribution:
-- Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's First
-- Link Network", Journal of Computational Science 19 (2017), 21-30.
-- DOI 10.1016/j.jocs.2016.12.001; arXiv:1605.00309.
------------------------------------------------------------------------

data TraversalEdgeClass : Set where
  currentEnglishFirstLinkCandidate
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
    primaryObjectStillRequired : Bool
    graphEdgeCreatesEvidenceAuthority : Bool
    graphEdgeCreatesSameObjectIdentity : Bool

open ScientistAcquisitionTraversal public

------------------------------------------------------------------------
-- Amy: the public POAMS object is a technical report.  On current English
-- Wikipedia, Technical report's first linked research concept in the defining
-- sentence is scientific research (the Research article/section).  This points
-- the acquisition outward from report content toward research-administration /
-- report-series metadata, but the graph does not itself supply the missing DAA.
------------------------------------------------------------------------

amyTechnicalReportToResearch : ScientistAcquisitionTraversal
amyTechnicalReportToResearch = scientist-acquisition-traversal
  "Amy Eskridge / POAMS"
  "exact MSFC EDAA/NF-1676B + attached STI/manuscript version"
  "technical report"
  "Q3099732"
  "research"
  "Q42240"
  currentEnglishFirstLinkCandidate
  "2026-09-11"
  "https://en.wikipedia.org/wiki/Technical_report"
  "001 Knowledge / 500 Science traversal; report itself remains NASA Subject Category 70 / Physics"
  "Use the Ibrahim edge only to rank report-series, research-administration and STI metadata surfaces. The conclusion-paying object remains the exact MSFC release-authorisation record."
  true false false

------------------------------------------------------------------------
-- Maiwald: spectroscopy has a current lead-level neighbour at electromagnetic
-- spectrum, while the unresolved scientific leaf is raw/reduced research data.
-- The graph therefore routes from topical spectroscopy toward data/metadata
-- provenance instead of treating affiliation or publication metadata as data
-- custody.
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
  "The topical first-link neighbourhood confirms the measurement domain but does not identify the data carrier. Snowball next through research-data and metadata repositories, using DOI/deposit identities rather than author-name matching."
  true false false

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
  true false false

------------------------------------------------------------------------
-- Reza: the patent object funnels toward intellectual-property / legal-record
-- surfaces.  This ranks patent-family and inventor-identity records above
-- secondary role repetition, while the JPL employment record remains separate.
------------------------------------------------------------------------

rezaPatentToIntellectualProperty : ScientistAcquisitionTraversal
rezaPatentToIntellectualProperty = scientist-acquisition-traversal
  "Monica Jacinto Reza / materials processing"
  "patent-inventor identity weld + primary JPL event-time role"
  "patent"
  "Q253623"
  "intellectual property"
  "Q131257"
  currentEnglishFirstLinkCandidate
  "2026-09-11"
  "https://en.wikipedia.org/wiki/Patent"
  "346.048 Intellectual property / 620 Engineering"
  "Follow exact patent-family, inventor-name, assignment and institutional identity records first; keep the independent JPL personnel/org-chart leaf separate from patent identity."
  true false false

------------------------------------------------------------------------
-- McCasland: Company register points immediately to companies and government-
-- mandated registration.  This makes the legal register/entity-history surface
-- the graph-ranked next step, not biographies or secondary client narratives.
------------------------------------------------------------------------

mccaslandCompanyRegisterToCompany : ScientistAcquisitionTraversal
mccaslandCompanyRegisterToCompany = scientist-acquisition-traversal
  "William Neil McCasland / DBE Consulting"
  "actual New Mexico entity/member-manager/ownership chronology"
  "company register"
  "Q1394657"
  "company"
  "Q783794"
  currentEnglishFirstLinkCandidate
  "2026-09-11"
  "https://en.wikipedia.org/wiki/Company_register"
  "338.7 Enterprises / 650 Management traversal only"
  "Prioritise the government company-register/entity-history carrier. Current biographies may guide the query but cannot pay founder, owner, manager or event-time corporate status."
  true false false

------------------------------------------------------------------------
-- Cross-lane metadata funnel.  Amy's DAA, Maiwald's CHORUS/NTRS harvest and
-- LeBlanc's freeze/role-state problem all depend on metadata/manifests rather
-- than another topical science paper.  Current Metadata exposes information/data
-- as its first general concepts; Wikidata Q180160 classifies metadata as data.
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
  "025.3 / 005.7 metadata coordinates; domain-specific Dewey remains authoritative only as traversal"
  true
  false
  "Ibrahim-style funneling says to inspect metadata/manifestation layers because multiple live frontiers converge there. Metadata can expose identifiers, dates, authorship and routing, but it does not manufacture the underlying manuscript, raw dataset, personnel state or succession relation."

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
    qidUsedAsSearchCoordinateOnly : Bool
    deweyUsedAsTraversalCoordinateOnly : Bool
    firstLinkAdjacencyCreatesProofDependency : Bool
    firstLinkAdjacencyCreatesSourceAuthority : Bool
    firstLinkTraversalMayRankNextAcquisition : Bool

open IbrahimScientistTraversalBoundary public

canonicalIbrahimScientistTraversalBoundary : IbrahimScientistTraversalBoundary
canonicalIbrahimScientistTraversalBoundary = ibrahim-scientist-traversal-boundary
  true true true true false true true false false true
