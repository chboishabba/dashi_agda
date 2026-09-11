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
    exactPrimaryRequestMayProceedFromPublicCoordinates : Bool

open PublicMetadataExhaustionFirewall public

canonicalPublicMetadataExhaustionFirewall : PublicMetadataExhaustionFirewall
canonicalPublicMetadataExhaustionFirewall = public-metadata-exhaustion-firewall
  false false false false true
