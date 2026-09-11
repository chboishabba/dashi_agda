module DASHI.Culture.AmyEskridgePOAMSRegisteredSTIAcquisitionRouteExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- AMY / POAMS REGISTERED-STI ACQUISITION ROUTE
--
-- NASA's current NTRS surface distinguishes publicly available content from
-- NTRS Registered Content, described by NASA as the complete STI collection for
-- authorized NASA users.  The public page also routes questions to the NASA STI
-- Information Desk.  This pays an acquisition route only: it does not establish
-- that the missing POAMS EDAA/NF-1676B object is present in registered content.
------------------------------------------------------------------------

record RegisteredSTIAcquisitionRoute : Set where
  constructor registered-sti-acquisition-route
  field
    targetPublicObject : String
    publicRepository : String
    registeredRepository : String
    nasaDescriptionOfRegisteredScope : String
    publicContactRoute : String
    centerRoutingContext : String
    nasaQid : String
    msfcQid : String
    deweyTraversal : String
    repeatedPublicSearchPerformed : Bool
    poamsSpecificEDAAFoundPublicly : Bool
    registeredContentMayContainTarget : Bool
    registeredContentProvesTargetExists : Bool
    publicSearchFailureProvesNoRecord : Bool
    nextAcquisition : String

open RegisteredSTIAcquisitionRoute public

poamsRegisteredSTIRoute : RegisteredSTIAcquisitionRoute
poamsRegisteredSTIRoute = registered-sti-acquisition-route
  "NASA/TM-20205010911 / M-1531 / NTRS 20205010911"
  "NASA Technical Reports Server public repository"
  "NASA STI Repository Registered Content / former NTRS-R"
  "NASA describes Registered Content as including the complete STI collection and restricting access to authorized NASA civil servants, contractors and grantees"
  "NASA STI Information Desk"
  "MSFC Propulsion Systems Department / Engineering Directorate -> STI Compliance and Distribution Services"
  "Q23548"
  "Q618696"
  "530 Physics / 629 Engineering traversal only"
  true false true false false
  "request/search POAMS-specific legacy EDAA/NF-1676B identity and its current STI/STRIVES archival representation through the NASA STI Information Desk and MSFC STI compliance/distribution route, keyed by M-1531, NTRS 20205010911, title, authors, SAA8-1519855 and funding MSFC-RMB-QUANTUM-SAA8-1519855-1; require attached-object/version and Amy-linked same-object receipts before promotion"

record RegisteredSTIBoundary : Set where
  constructor registered-sti-boundary
  field
    completeCollectionDescriptionImpliesSpecificEDAAExists : Bool
    restrictedAccessImpliesSuppression : Bool
    publicSearchFailureImpliesDeletion : Bool
    registeredRouteMayGuideTargetedAcquisition : Bool

open RegisteredSTIBoundary public

canonicalRegisteredSTIBoundary : RegisteredSTIBoundary
canonicalRegisteredSTIBoundary = registered-sti-boundary false false false true

------------------------------------------------------------------------
-- Legacy EDAA / current STRIVES archaeology.
--
-- Historical NPR 2200.2D documents the DAA/EDAA review and NF-1676/NF-1676B
-- lineage.  NASA marks 2200.2D obsolete.  Current NPR 2200.2E, effective
-- 2021-12-17 and revalidated through 2031, defines STRIVES Review as NASA's
-- dissemination/release approval process and NF-1676 as the requisite form.
-- NASA STI Compliance and Distribution Services separately states that STRIVES
-- standardizes STI submission, review and approval across all ten field centers.
-- These are successive process/system manifestations; identifier or byte
-- identity across them is not assumed.
------------------------------------------------------------------------

record ReleaseSystemArchaeology : Set where
  constructor release-system-archaeology
  field
    historicalReleaseMechanism : String
    historicalFormIdentity : String
    historicalSystemIdentity : String
    currentSubmissionReviewSystem : String
    currentServiceOwner : String
    currentPublicContact : String
    exactPOAMSLegacyEDAAIdentityPaid : Bool
    exactPOAMSSTRIVESRecordPaid : Bool
    legacyAndCurrentRecordSameObjectPaid : Bool
    policyRequiresReleaseReview : Bool
    daaRepresentativeTracksAndTransfersAssociatedSTI : Bool
    currentSystemCanGuideLegacyAcquisition : Bool
    systemMigrationImpliesRecordSuppression : Bool
    acquisitionTarget : String

open ReleaseSystemArchaeology public

poamsReleaseSystemArchaeology : ReleaseSystemArchaeology
poamsReleaseSystemArchaeology = release-system-archaeology
  "Document Availability Authorization review for NASA STI"
  "NASA Form NF-1676 / NF-1676B"
  "Electronic Document Availability Authorization (EDAA) documented by historical NPR 2200.2D"
  "Scientific, Technical and Research Information discoVEry System (STRIVES) under current NPR 2200.2E"
  "NASA STI Compliance and Distribution Services"
  "NASA STI Information Desk"
  false false false true true true false
  "recover the POAMS legacy EDAA/NF-1676B identity and ask NASA STI/MSFC for the corresponding current STRIVES/STI archival representation, associated STI attachment/version, review-history metadata and transfer/release relationship; do not assume EDAA and STRIVES identifiers are identical"

------------------------------------------------------------------------
-- Current-policy / historical-policy boundary.
------------------------------------------------------------------------

record ReleasePolicyVersionState : Set where
  constructor release-policy-version-state
  field
    historicalDirective : String
    historicalDirectiveStatus : String
    currentDirective : String
    currentDirectiveEffectiveDate : String
    currentDirectiveExpirationDate : String
    currentReleaseReviewDefinition : String
    currentRequisiteForm : String
    currentPolicyAppliesToNASAcenters : Bool
    historicalDirectiveMayBeUsedAsCurrentPolicy : Bool
    historicalDirectiveMayDocumentLegacyEDAAProcess : Bool
    currentDirectivePaysPOAMSLegacyRecordIdentity : Bool
    currentDirectiveCanRouteArchivalCrosswalkSearch : Bool

open ReleasePolicyVersionState public

canonicalReleasePolicyVersionState : ReleasePolicyVersionState
canonicalReleasePolicyVersionState = release-policy-version-state
  "NPR 2200.2D"
  "NASA marks this directive obsolete / no longer used; retained here only for historical DAA/EDAA archaeology"
  "NPR 2200.2E — Requirements for Documentation, Approval and Dissemination of Scientific and Technical Information, revalidated with Change 2"
  "2021-12-17"
  "2031-12-17"
  "STRIVES Review = dissemination or release approval process by which NASA determines restrictions, if any, on a document"
  "NASA Form NF-1676"
  true false true false true

record ReleaseSystemBoundary : Set where
  constructor release-system-boundary
  field
    edaaIdentifierEqualsStrivesIdentifierWithoutReceipt : Bool
    currentStrivesSurfaceProvesLegacyEdaaNumber : Bool
    legacyPolicyRequirementProvesSpecificRecordLocated : Bool
    systemMigrationProvesDeletionOrSuppression : Bool
    crossSystemIdentityMayBePaidByPrimaryNASARecord : Bool

open ReleaseSystemBoundary public

canonicalReleaseSystemBoundary : ReleaseSystemBoundary
canonicalReleaseSystemBoundary = release-system-boundary false false false false true
