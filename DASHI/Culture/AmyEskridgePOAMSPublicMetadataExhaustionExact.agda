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
-- NTRS public citation records from the same centre show both positive and
-- negative EDAA-exposure cases inside the Technical Memorandum document class.
-- Therefore the POAMS omission is a manifestation-level observation, not a
-- document-class anomaly and not evidence that an approval record was absent.
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

msfcTMPeer20180008760 : PublicMSFCEDAAPeerControl
msfcTMPeer20180008760 = public-msfc-edaa-peer-control
  "NTRS 20180008760 / NASA/TM-2018-219998 / M-1479"
  "Technical Memorandum (TM)"
  "MSFC-E-DAA-TN64271"
  "https://ntrs.nasa.gov/citations/20180008760"
  true true

msfcTMPeer20180005693 : PublicMSFCEDAAPeerControl
msfcTMPeer20180005693 = public-msfc-edaa-peer-control
  "NTRS 20180005693 / NASA/TM-2018-219958 / M-1462"
  "Technical Memorandum (TM)"
  "MSFC-E-DAA-TN59151"
  "https://ntrs.nasa.gov/citations/20180005693"
  true true

msfcTMPeer20180002207 : PublicMSFCEDAAPeerControl
msfcTMPeer20180002207 = public-msfc-edaa-peer-control
  "NTRS 20180002207 / NASA/TM-2018-219882 / M-1458"
  "Technical Memorandum (TM)"
  "MSFC-E-DAA-TN52539"
  "https://ntrs.nasa.gov/citations/20180002207"
  true true

msfcTMPeer20200001187 : PublicMSFCEDAAPeerControl
msfcTMPeer20200001187 = public-msfc-edaa-peer-control
  "NTRS 20200001187 / NASA/TM-2020-220471"
  "Technical Memorandum (TM)"
  "MSFC-E-DAA-TN77428"
  "https://ntrs.nasa.gov/citations/20200001187"
  true true

-- Same-center/same-document-class negative controls.  Their current public
-- NTRS records expose NASA/TM and/or M-series identifiers but no EDAA number.
-- The empty EDAA string means only "not exposed on this public manifestation".

msfcTMPeer20200000049 : PublicMSFCEDAAPeerControl
msfcTMPeer20200000049 = public-msfc-edaa-peer-control
  "NTRS 20200000049 / NASA/TM-2019-220142 / M-1494"
  "Technical Memorandum (TM)"
  ""
  "https://ntrs.nasa.gov/citations/20200000049"
  true false

msfcTMPeer20200000050 : PublicMSFCEDAAPeerControl
msfcTMPeer20200000050 = public-msfc-edaa-peer-control
  "NTRS 20200000050 / NASA/TM-2019-220548 / M-1495"
  "Technical Memorandum (TM)"
  ""
  "https://ntrs.nasa.gov/citations/20200000050"
  true false

msfcTMPeer20200000051 : PublicMSFCEDAAPeerControl
msfcTMPeer20200000051 = public-msfc-edaa-peer-control
  "NTRS 20200000051 / NASA/TM-2019-220551 / M-1498"
  "Technical Memorandum (TM)"
  ""
  "https://ntrs.nasa.gov/citations/20200000051"
  true false

record PublicMetadataOmissionComparison : Set where
  constructor public-metadata-omission-comparison
  field
    peerMSFCRecordsPubliclyExposeEDAA : Bool
    poamsPublicRecordExposesEDAA : Bool
    sameDocumentTypeTMComparatorLocated : Bool
    sameDocumentTypeTMNegativeComparatorLocated : Bool
    sameTypeExposureIsHeterogeneous : Bool
    omissionIsManifestationSpecificObservation : Bool
    omissionProvesNoUnderlyingEDAA : Bool
    omissionProvesSuppression : Bool
    boundedReading : String

open PublicMetadataOmissionComparison public

canonicalPOAMSMetadataOmissionComparison : PublicMetadataOmissionComparison
canonicalPOAMSMetadataOmissionComparison = public-metadata-omission-comparison
  true false true true true true false false
  "Public MSFC Technical Memoranda are heterogeneous in EDAA exposure. NTRS 20200001187 exposes MSFC-E-DAA-TN77428 alongside NASA/TM-2020-220471, while NTRS 20200000049, 20200000050 and 20200000051 expose NASA/TM and M-series identifiers without a public EDAA field. POAMS NTRS 20205010911 likewise currently exposes M-1531 and NASA-TM-20205010911 without an EDAA field. Therefore document type does not determine public EDAA exposure, and POAMS is not established as anomalous by this field alone. The omission remains manifestation-specific and cannot be promoted to absence of an underlying approval record, interpolation of an identifier, deletion, or suppression."

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
  "NASA STI Information Desk / MSFC STI Compliance and Distribution Services: request release-authorization metadata keyed to NTRS 20205010911, M-1531, full title, R.H. Eskridge / M.A. Nelson / M.P. Schoenfeld, SAA8-1519855 and MSFC-RMB-QUANTUM-SAA8-1519855-1; seek exact NF-1676/STRIVES approval identity or migrated EDAA lineage, approval/routing dates and attached manuscript/version"

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
