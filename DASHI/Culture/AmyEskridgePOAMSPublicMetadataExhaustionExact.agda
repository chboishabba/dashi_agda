module DASHI.Culture.AmyEskridgePOAMSPublicMetadataExhaustionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- AMY ESKRIDGE / POAMS PUBLIC-METADATA EXHAUSTION
--
-- Thin acquisition-state owner.  This records what the public NTRS citation
-- surface does and does not expose.  It must not turn repeated public-search
-- failure into evidence that an EDAA/NF-1676B record never existed.
------------------------------------------------------------------------

record PublicMetadataSurface : Set where
  constructor public-metadata-surface
  field
    publicObject : String
    directLink : String
    sourceClass : String
    documentIdentifier : String
    reportNumber : String
    fundingNumber : String
    acquisitionSource : String
    subjectCategory : String
    publicDistributionPaid : Bool
    exactEDAAIdentifierExposed : Bool
    attachedDAAObjectExposed : Bool
    amyReviewIdentityExposed : Bool
    qidCoordinate : String
    deweyTraversal : String

open PublicMetadataSurface public

poamsPublicNTRSSurface : PublicMetadataSurface
poamsPublicNTRSSurface = public-metadata-surface
  "A Study of the Pope-Osborne Angular Momentum Synthesis Theory (POAMS) Including a Mathematical Reformulation and Validation Experiment"
  "https://ntrs.nasa.gov/citations/20205010911"
  "primary NASA government citation record"
  "NTRS 20205010911 / NASA-TM-20205010911"
  "M-1531"
  "MSFC-RMB-QUANTUM-SAA8-1519855-1"
  "Marshall Space Flight Center"
  "Physics (General)"
  true false false false
  "NASA Q23548; MSFC Q618696; Amy person QID unresolved"
  "530 Physics / 629 Engineering traversal only"

------------------------------------------------------------------------
-- Public-MSFC peer metadata controls.
--
-- NTRS public citation records from the same centre visibly expose Marshall
-- EDAA identifiers in the public Report/Patent Number field, e.g.
--   20180001588 -> MSFC-E-DAA-TN51196
--   20180001994 -> MSFC-E-DAA-TN53283
--   20190033128 -> MSFC-E-DAA-TN73753
-- These peers establish that EDAA identifiers can be public NTRS metadata.
-- They do not prove that every MSFC document type, every historical release,
-- or POAMS specifically must expose one.  A same-document-type Technical
-- Memorandum comparator was not located in the present public search pass.
------------------------------------------------------------------------

record PublicMSFCEDAAPeerControl : Set where
  constructor public-msfc-edaa-peer-control
  field
    peerDocumentId : String
    peerDocumentType : String
    peerEDAANumber : String
    peerDirectLink : String
    acquisitionSourceMSFC : Bool
    edaaVisibleInPublicReportField : Bool

open PublicMSFCEDAAPeerControl public

msfcPeer20180001588 : PublicMSFCEDAAPeerControl
msfcPeer20180001588 = public-msfc-edaa-peer-control
  "NTRS 20180001588"
  "Presentation"
  "MSFC-E-DAA-TN51196"
  "https://ntrs.nasa.gov/citations/20180001588"
  true true

msfcPeer20180001994 : PublicMSFCEDAAPeerControl
msfcPeer20180001994 = public-msfc-edaa-peer-control
  "NTRS 20180001994"
  "Presentation"
  "MSFC-E-DAA-TN53283"
  "https://ntrs.nasa.gov/citations/20180001994"
  true true

msfcPeer20190033128 : PublicMSFCEDAAPeerControl
msfcPeer20190033128 = public-msfc-edaa-peer-control
  "NTRS 20190033128"
  "Technical Publication"
  "MSFC-E-DAA-TN73753"
  "https://ntrs.nasa.gov/citations/20190033128"
  true true

record PublicMetadataOmissionComparison : Set where
  constructor public-metadata-omission-comparison
  field
    peerMSFCRecordsPubliclyExposeEDAA : Bool
    poamsPublicRecordExposesEDAA : Bool
    sameDocumentTypeTMComparatorLocated : Bool
    omissionIsManifestationSpecificObservation : Bool
    omissionProvesNoUnderlyingEDAA : Bool
    omissionProvesSuppression : Bool
    boundedReading : String

open PublicMetadataOmissionComparison public

canonicalPOAMSMetadataOmissionComparison : PublicMetadataOmissionComparison
canonicalPOAMSMetadataOmissionComparison = public-metadata-omission-comparison
  true false false true false false
  "Public MSFC peers establish that EDAA numbers can be exposed in NTRS Report/Patent Number metadata, while POAMS NTRS 20205010911 currently exposes M-1531 and NASA-TM-20205010911 without an EDAA field. No same-document-type Technical Memorandum comparator was located in this pass, so the observation is manifestation-specific and cannot be promoted to a claim that POAMS lacked an EDAA or that its metadata was suppressed."

record PublicSearchBoundary : Set where
  constructor public-search-boundary
  field
    exactTitleSearchPerformed : Bool
    documentIdSearchPerformed : Bool
    reportNumberSearchPerformed : Bool
    fundingNumberSearchPerformed : Bool
    authorNamespaceSearchPerformed : Bool
    edaaFamilySearchPerformed : Bool
    publicIndexedEDAALocated : Bool
    publicSearchFailureImpliesNoEDAAEverExisted : Bool
    publicSearchFailureImpliesSuppression : Bool
    registeredSTIOrComplianceRouteRemainsAdmissible : Bool
    nextAcquisition : String

open PublicSearchBoundary public

canonicalPOAMSPublicSearchBoundary : PublicSearchBoundary
canonicalPOAMSPublicSearchBoundary = public-search-boundary
  true true true true true true
  false false false true
  "NASA STI Information Desk / MSFC STI Compliance and Distribution Services: request release-authorization metadata keyed to NTRS 20205010911, M-1531, full title, R.H. Eskridge / M.A. Nelson / M.P. Schoenfeld, SAA8-1519855 and MSFC-RMB-QUANTUM-SAA8-1519855-1; seek exact EDAA/NF-1676B identifier, approval/routing dates and attached manuscript/version"

record PublicMetadataExhaustionFirewall : Set where
  constructor public-metadata-exhaustion-firewall
  field
    ntrsPublicCitationEqualsCompleteAdministrativeFile : Bool
    missingPublicFieldProvesMissingRegisteredField : Bool
    registeredContentDescriptionProvesSpecificPOAMSRecordPresent : Bool
    adjacentMSFCEDAANumbersMayBeInterpolated : Bool
    peerMSFCEDAAPresenceProvesPOAMSEDAAPresence : Bool
    exactPrimaryRequestMayProceedFromPublicCoordinates : Bool

open PublicMetadataExhaustionFirewall public

canonicalPublicMetadataExhaustionFirewall : PublicMetadataExhaustionFirewall
canonicalPublicMetadataExhaustionFirewall = public-metadata-exhaustion-firewall
  false false false false false true
