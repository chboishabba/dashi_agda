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
-- EDAA identifiers in the public Report/Patent Number field.  The control set
-- now includes same-document-type Technical Memoranda, removing the earlier
-- comparator-class gap while retaining the no-interpolation/no-suppression
-- firewalls for POAMS itself.
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
  true false true true false false
  "Multiple public MSFC Technical Memoranda expose MSFC-E-DAA-TN identifiers alongside NASA/TM and/or M-series report numbers, including NTRS 20180008760 (M-1479 / MSFC-E-DAA-TN64271), 20180005693 (M-1462 / MSFC-E-DAA-TN59151), 20180002207 (M-1458 / MSFC-E-DAA-TN52539), and 20200001187 (NASA/TM-2020-220471 / MSFC-E-DAA-TN77428). POAMS NTRS 20205010911 currently exposes M-1531 and NASA-TM-20205010911 without an EDAA field. This strengthens the observation that the missing public POAMS EDAA field is not merely explained by document type, but it still cannot be promoted to a claim that POAMS lacked an underlying approval record, that an identifier can be interpolated, or that metadata was suppressed."

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
