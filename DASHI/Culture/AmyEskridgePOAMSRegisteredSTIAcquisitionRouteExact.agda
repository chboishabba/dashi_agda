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
-- that the missing POAMS approval record is present in registered content.
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
    poamsSpecificApprovalFoundPublicly : Bool
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
  "request/search the POAMS-specific NF-1676/STRIVES approval identity and any migrated legacy EDAA/NF-1676B lineage through the NASA STI Information Desk and MSFC STI compliance/distribution route, keyed by M-1531, NTRS 20205010911, title, authors, SAA8-1519855 and funding MSFC-RMB-QUANTUM-SAA8-1519855-1; require attached-object/version and Amy-linked same-object receipts before promotion"

record RegisteredSTIBoundary : Set where
  constructor registered-sti-boundary
  field
    completeCollectionDescriptionImpliesSpecificApprovalExists : Bool
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
-- lineage. NASA's 2020 CIO annual report says STRIVES was fully adopted across
-- the agency by May 2020, NTRS transitioned to the STRIVES STI Repository by
-- July 2020, and legacy STI applications were retired by August 2020. Current
-- NPR 2200.2E defines NF-1676 as the approval workflow implemented in STRIVES.
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
    currentSystemCanGuideLegacyAcquisition : Bool
    systemMigrationImpliesRecordSuppression : Bool
    acquisitionTarget : String

open ReleaseSystemArchaeology public

poamsReleaseSystemArchaeology : ReleaseSystemArchaeology
poamsReleaseSystemArchaeology = release-system-archaeology
  "Document Availability Authorization / NF-1676 release review for NASA STI"
  "NASA Form NF-1676 / legacy NF-1676B"
  "Electronic Document Availability Authorization (EDAA), predecessor system at Marshall"
  "Scientific, Technical and Research Information discoVEry System (STRIVES)"
  "NASA STI Compliance and Distribution Services"
  "NASA STI Information Desk"
  false false false true true false
  "recover the POAMS NF-1676/STRIVES approval identity current at the 2020 acquisition/review period and, only if necessary, its migrated legacy EDAA/NF-1676B lineage; recover associated STI attachment/version and review-history metadata; do not assume EDAA and STRIVES identifiers are identical"

------------------------------------------------------------------------
-- 2020 transition chronology: this changes the preferred acquisition target.
------------------------------------------------------------------------

record ReleaseSystemTransition2020 : Set where
  constructor release-system-transition-2020
  field
    strivesFullyAdoptedBy : String
    ntrsTransitionedBy : String
    legacyApplicationsRetiredBy : String
    poamsReportedReviewMonth : String
    poamsNtrsAcquisitionDate : String
    poamsPublicationDate : String
    poamsReviewAfterAgencySTRIVESAdoption : Bool
    poamsAcquisitionAfterLegacyRetirement : Bool
    strongestExpectedApprovalNamespace : String
    legacyEDAAStillRelevantAsPredecessorLineage : Bool
    legacyEDAAIsPreferredPrimaryTarget : Bool
    currentSTRIVESIdentityLocated : Bool
    transitionChronologyCreatesSpecificApprovalId : Bool

open ReleaseSystemTransition2020 public

poamsReleaseSystemTransition2020 : ReleaseSystemTransition2020
poamsReleaseSystemTransition2020 = release-system-transition-2020
  "2020-05"
  "2020-07"
  "2020-08"
  "2020-09 (reported Amy review-object timing; exact same-object identity unpaid)"
  "2020-12-01"
  "2021-11-01"
  true true
  "NF-1676 / STRIVES approval identity or migrated STRIVES-era release metadata"
  true false false false

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
    currentDirectivePaysPOAMSApprovalIdentity : Bool
    currentDirectiveCanRouteArchivalCrosswalkSearch : Bool

open ReleasePolicyVersionState public

canonicalReleasePolicyVersionState : ReleasePolicyVersionState
canonicalReleasePolicyVersionState = release-policy-version-state
  "NPR 2200.2D"
  "NASA marks this directive obsolete / no longer used; retained here only for historical DAA/EDAA archaeology"
  "NPR 2200.2E — Requirements for Documentation, Approval and Dissemination of Scientific and Technical Information, revalidated with Change 2"
  "2021-12-17"
  "2031-12-17"
  "NF-1676 is the approval workflow implemented through STRIVES for NASA STI release/dissemination"
  "NASA Form NF-1676"
  true false true false true

------------------------------------------------------------------------
-- Archival pairing obligation.
--
-- NPR 2200.2E requires Center STRIVES representatives to track, file and
-- transfer the NF-1676 together with its associated STI after approval.  It
-- also requires the Center to ensure that NASA STI Program receives STI and
-- corresponding NF-1676 forms before Center retention disposal.  This is a
-- strong route/custody obligation, but it still does not prove that the exact
-- historical POAMS form remains extant or that its identifier is public.
------------------------------------------------------------------------

record ApprovalArchivalPairingState : Set where
  constructor approval-archival-pairing-state
  field
    policySource : String
    pairedObjects : String
    centerTracksFilesAndTransfersPair : Bool
    nasaSTIReceivesCorrespondingFormsBeforeCenterDisposal : Bool
    policySupportsPairedArchivalSearch : Bool
    policyProvesExactPOAMSFormCurrentlyExtant : Bool
    policyProvesPublicIdentifierExposure : Bool
    policyProvesAmySameObject : Bool
    acquisitionConsequence : String

open ApprovalArchivalPairingState public

poamsApprovalArchivalPairing : ApprovalArchivalPairingState
poamsApprovalArchivalPairing = approval-archival-pairing-state
  "NPR 2200.2E, Center STI Manager and Center STRIVES Representative responsibilities"
  "approved NF-1676 plus associated STI object/version"
  true true true false false false
  "request the paired approval-and-STI archival crosswalk for NASA/TM-20205010911 from STI Compliance and Distribution Services / the MSFC STRIVES lineage: NF-1676/STRIVES record identity, disposition, approver/routing chronology, exact associated STI attachment/version, and any migrated legacy EDAA lineage; only after that compare the recovered reviewed object with the independently reported Amy review object"

record ReleaseSystemBoundary : Set where
  constructor release-system-boundary
  field
    edaaIdentifierEqualsStrivesIdentifierWithoutReceipt : Bool
    currentStrivesSurfaceProvesLegacyEdaaNumber : Bool
    historicalEdaaRequirementProvesPOAMSUsedEdaaInLate2020 : Bool
    policyRequirementProvesSpecificRecordLocated : Bool
    systemMigrationProvesDeletionOrSuppression : Bool
    crossSystemIdentityMayBePaidByPrimaryNASARecord : Bool

open ReleaseSystemBoundary public

canonicalReleaseSystemBoundary : ReleaseSystemBoundary
canonicalReleaseSystemBoundary = release-system-boundary false false false false false true
