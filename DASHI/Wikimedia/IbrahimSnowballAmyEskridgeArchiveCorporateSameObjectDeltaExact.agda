module DASHI.Wikimedia.IbrahimSnowballAmyEskridgeArchiveCorporateSameObjectDeltaExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballInvestigativeClaimSourceLineageBidiExact as Claim
import DASHI.Wikimedia.IbrahimSnowballAmyEskridgeClaimLineageClassificationSystemBidiExact as Prior
import DASHI.Culture.AmyEskridgeApplicationTransformationExact as Amy

------------------------------------------------------------------------
-- THIN AMY DELTA AFTER DIRECT SOURCE INSPECTION
--
-- This file does not reopen the general provenance ontology.  It adds only the
-- concrete residuals exposed by inspecting the issuer-filed SEC Form D and by
-- locating the September-2020 social-media archive through a source-lineage
-- audit:
--   1. captured archive identity != original carrier/provenance/authorship;
--   2. corporate officer/entity identity != research validation/derivative ID;
--   3. temporal/topic adjacency != same-object identity.
--
-- The first unpaid application leaf therefore remains the exact Institute
-- derivative/application object identity.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy archive-corporate same-object delta"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create source authenticity, same-object continuity, corporate truth or scientific validation")

secQid : Identity.ExternalIdentityDemand
secQid = mkQid "United States Securities and Exchange Commission" "Q953944"

waybackMachineQid : Identity.ExternalIdentityDemand
waybackMachineQid = mkQid "Wayback Machine" "Q648266"

instituteCik : Identity.ExternalIdentityDemand
instituteCik = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy archive-corporate same-object delta"
  "official issuer identifier"
  "Institute, P.B.C. SEC CIK"
  Identity.officialIdentifier
  (Identity.verified "0001771320"
    "SEC Form D issuer identity inspected directly 2026-09-11")

instituteFormDAccession : Identity.ExternalIdentityDemand
instituteFormDAccession = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy archive-corporate same-object delta"
  "official filing identifier"
  "Institute, P.B.C. 2019 Form D filing"
  Identity.officialIdentifier
  (Identity.verified "000177132019000001"
    "SEC archive path / filing object inspected directly 2026-09-11")

secFormDCanonicalLink : Identity.ExternalIdentityDemand
secFormDCanonicalLink = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy archive-corporate same-object delta"
  "canonical primary-source link"
  "Institute, P.B.C. SEC Form D"
  Identity.canonicalURL
  (Identity.verified
    "https://www.sec.gov/Archives/edgar/data/1771320/000177132019000001/xslFormDX01/primary_doc.xml"
    "official SEC filing inspected directly 2026-09-11")

captured2020ArchiveCarrier : Identity.ExternalIdentityDemand
captured2020ArchiveCarrier = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy archive-corporate same-object delta"
  "captured artifact identity"
  "September 18 2020 Wayback capture of Alien_Scientist post 1306981668419301379"
  Identity.canonicalURL
  (Identity.candidate
    "https://web.archive.org/web/20200918154520id_/https://twitter.com/Alien_Scientist/status/1306981668419301379"
    "exact archive URL is listed by Troth Record TR-0013 as a captured source; direct Wayback content was not independently retrievable in this inspection environment, so original-carrier/authorship status remains unpaid")

originalAmyStatementCarrier : Identity.ExternalIdentityDemand
originalAmyStatementCarrier = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy archive-corporate same-object delta"
  "original first-party carrier identity"
  "original Amy-authored private-maturation/release-review statement carrier"
  Identity.canonicalURL
  (Identity.unresolved
    "located archive is an associate-posted screenshot attributed to Amy; no exact original Amy-owned post/document carrier paid")

------------------------------------------------------------------------
-- Dewey remains unresolved and separate from SEC/NASA classification systems.
------------------------------------------------------------------------

corporateFilingDewey : Dewey.DeweyCoordinate
corporateFilingDewey = Dewey.mkUnresolvedDewey
  "Institute, P.B.C. SEC Form D / corporate continuity"
  "SEC filing classification and CIK are official regulatory identifiers, not Dewey coordinates; no exact DDC promoted"

archiveCaptureDewey : Dewey.DeweyCoordinate
archiveCaptureDewey = Dewey.mkUnresolvedDewey
  "captured social-media archive / source-lineage evidence"
  "archive carrier spans web archiving and investigation; no exact inspected DDC promoted"

------------------------------------------------------------------------
-- Source attribution.
------------------------------------------------------------------------

secInstituteFormDSource : Attribution.AttributedSource
secInstituteFormDSource = Attribution.mkNoDOISource
  "Institute, P.B.C.; Amy Eskridge Pettigrew (authorized signer)"
  "Form D Notice of Exempt Offering of Securities"
  "U.S. Securities and Exchange Commission EDGAR; CIK 0001771320"
  "2019"
  "https://www.sec.gov/Archives/edgar/data/1771320/000177132019000001/xslFormDX01/primary_doc.xml"
  Attribution.governmentSource
  "issuer-filed primary regulatory carrier establishing bounded corporate/entity facts: Institute, P.B.C. identity, 2018 Delaware incorporation claim, Amy's President/executive-officer/director role, and offering metadata; SEC warns the information is issuer-supplied and not necessarily reviewed, and the filing does not establish research validation, R&D award, apparatus identity or private derivative-object identity"
  Attribution.publicAttribution

trothArchiveLocatorSource : Attribution.AttributedSource
trothArchiveLocatorSource = Attribution.mkNoDOISource
  "Troth"
  "What the public record establishes about Amy Eskridge — TR-0013"
  "Troth Record TR-0013"
  "2026"
  "https://troth.press/records/tr-0013/"
  Attribution.namedSourceKind "secondary investigative source-lineage audit"
  "secondary locator/audit used to retain the exact Wayback URL and its bounded classification as an associate-posted screenshot attributed to Amy; does not convert the archive into an original Amy-owned carrier and does not prove the statement's substantive claims"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Regression 1: captured artifact identity cannot recover original provenance.
------------------------------------------------------------------------

data ArchiveCase : Set where
  sameCaptureAssociatePosted sameCaptureOriginalFirstParty : ArchiveCase

data CaptureSurface : Set where sameCapturedScreenshot : CaptureSurface
data OriginalProvenance : Set where associatePostedAttributed originalFirstPartyAuthored : OriginalProvenance

captureSurface : ArchiveCase → CaptureSurface
captureSurface _ = sameCapturedScreenshot

originalProvenance : ArchiveCase → OriginalProvenance
originalProvenance sameCaptureAssociatePosted = associatePostedAttributed
originalProvenance sameCaptureOriginalFirstParty = originalFirstPartyAuthored

archiveProvenanceDefect : INF.NonFactorabilityWitness captureSurface originalProvenance
archiveProvenanceDefect = INF.nonFactorabilityWitness
  sameCaptureAssociatePosted sameCaptureOriginalFirstParty refl (λ ())

capturedArtifactCannotFactorOriginalCarrierProvenance :
  INF.FactorsThrough captureSurface originalProvenance → ⊥
capturedArtifactCannotFactorOriginalCarrierProvenance =
  INF.witnessRulesOutEveryFlatFactorisation archiveProvenanceDefect

------------------------------------------------------------------------
-- Regression 2: corporate role/entity continuity cannot recover scientific
-- validation or the private derivative object's identity.
------------------------------------------------------------------------

data CorporateCase : Set where
  sameCorporateRoleDerivativeUnknown sameCorporateRoleDerivativeKnown : CorporateCase

data CorporateSurface : Set where samePresidentDirectorEntityReceipt : CorporateSurface
data TechnicalObjectStatus : Set where technicalDerivativeUnidentified technicalDerivativeIdentified : TechnicalObjectStatus

corporateSurface : CorporateCase → CorporateSurface
corporateSurface _ = samePresidentDirectorEntityReceipt

technicalObjectStatus : CorporateCase → TechnicalObjectStatus
technicalObjectStatus sameCorporateRoleDerivativeUnknown = technicalDerivativeUnidentified
technicalObjectStatus sameCorporateRoleDerivativeKnown = technicalDerivativeIdentified

corporateTechnicalDefect : INF.NonFactorabilityWitness corporateSurface technicalObjectStatus
corporateTechnicalDefect = INF.nonFactorabilityWitness
  sameCorporateRoleDerivativeUnknown sameCorporateRoleDerivativeKnown refl (λ ())

corporateRoleCannotFactorPrivateDerivativeIdentity :
  INF.FactorsThrough corporateSurface technicalObjectStatus → ⊥
corporateRoleCannotFactorPrivateDerivativeIdentity =
  INF.witnessRulesOutEveryFlatFactorisation corporateTechnicalDefect

------------------------------------------------------------------------
-- Regression 3: temporal + topic adjacency cannot recover same-object identity.
--
-- The Amy-attributed screenshot is dated September 2020.  NASA NTRS lists
-- NASA/TM-20205010911 as acquired December 1, 2020 and published November 1,
-- 2021.  That temporal proximity plus broad gravity/POAMS adjacency is a search
-- cue only; the public screenshot supplies no title/case number and Amy is not a
-- named author on the NASA memorandum.
------------------------------------------------------------------------

data TimelineCase : Set where
  sameTimelineAdjacentDifferentObjects sameTimelineAdjacentSameObject : TimelineCase

data TimelineSurface : Set where sameLate2020GravityReleaseNeighbourhood : TimelineSurface
data SameObjectStatus : Set where sameObjectUnpaid sameObjectPaid : SameObjectStatus

timelineSurface : TimelineCase → TimelineSurface
timelineSurface _ = sameLate2020GravityReleaseNeighbourhood

sameObjectStatus : TimelineCase → SameObjectStatus
sameObjectStatus sameTimelineAdjacentDifferentObjects = sameObjectUnpaid
sameObjectStatus sameTimelineAdjacentSameObject = sameObjectPaid

timelineSameObjectDefect : INF.NonFactorabilityWitness timelineSurface sameObjectStatus
timelineSameObjectDefect = INF.nonFactorabilityWitness
  sameTimelineAdjacentDifferentObjects sameTimelineAdjacentSameObject refl (λ ())

temporalTopicAdjacencyCannotFactorSameObjectIdentity :
  INF.FactorsThrough timelineSurface sameObjectStatus → ⊥
temporalTopicAdjacencyCannotFactorSameObjectIdentity =
  INF.witnessRulesOutEveryFlatFactorisation timelineSameObjectDefect

------------------------------------------------------------------------
-- Ordered payment remains unchanged.
------------------------------------------------------------------------

priorBoundary : Prior.AmyIbrahimClaimLineageBoundary
priorBoundary = Prior.canonicalAmyIbrahimClaimLineageBoundary

amyApplicationFrontier : Amy.AmyApplicationTransformationFrontier
amyApplicationFrontier = Amy.canonicalAmyApplicationTransformationFrontier

exactDerivativeIdentityStillFirstUnpaid : Amy.AmyApplicationReverseTarget
exactDerivativeIdentityStillFirstUnpaid = Amy.firstAmyApplicationMissingLeaf

sameObjectRouter : Claim.ClaimResidualRouter
sameObjectRouter = Claim.mkClaimResidualRouter
  "whether the September-2020 Amy-attributed private-maturation statement and NASA/TM-20205010911 refer to the same technical derivative object"
  "September-2020 captured attributed screenshot + NASA NTRS acquisition 2020-12-01/publication 2021-11-01 + topic adjacency"
  "matching title/case/review identifier, authorship/release chain, explicit cross-reference, or apparatus/data same-object receipt"

------------------------------------------------------------------------
-- Reverse constraints.
------------------------------------------------------------------------

record AmyArchiveReverseConstraint : Set where
  constructor amy-archive-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open AmyArchiveReverseConstraint public

archiveConstraint : AmyArchiveReverseConstraint
archiveConstraint = amy-archive-reverse-constraint
  "Archive / source criticism"
  "archive timestamp, captured page identity, embedded screenshot, uploader/poster identity, attributed speaker/author, original carrier and proposition truth remain distinct"
  false

corporateConstraint : AmyArchiveReverseConstraint
corporateConstraint = amy-archive-reverse-constraint
  "Corporate / institutional records"
  "issuer identity, officer/director role, filing assertions, financing metadata, technical programme identity, research award and validation remain distinct"
  false

sameObjectConstraint : AmyArchiveReverseConstraint
sameObjectConstraint = amy-archive-reverse-constraint
  "Investigation / same-object continuity"
  "time adjacency, topical overlap, surname/institution adjacency and publication chronology are candidate-routing cues; exact object identity requires an explicit same-object receipt"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data ArchiveCaptureMeansOriginalCarrier : Set where
data ArchiveCaptureMeansStatementTrue : Set where
data SecOfficerRoleMeansResearchValidated : Set where
data SecOfferingMeansResearchAward : Set where
data Late2020TimingMeansSameObject : Set where
data CandidateArchiveMeansVerifiedOriginal : Set where

archiveCaptureDoesNotCreateOriginalCarrier : ArchiveCaptureMeansOriginalCarrier → ⊥
archiveCaptureDoesNotCreateOriginalCarrier ()

archiveCaptureDoesNotCreateStatementTruth : ArchiveCaptureMeansStatementTrue → ⊥
archiveCaptureDoesNotCreateStatementTruth ()

secOfficerRoleDoesNotCreateResearchValidation : SecOfficerRoleMeansResearchValidated → ⊥
secOfficerRoleDoesNotCreateResearchValidation ()

secOfferingDoesNotCreateResearchAward : SecOfferingMeansResearchAward → ⊥
secOfferingDoesNotCreateResearchAward ()

late2020TimingDoesNotCreateSameObject : Late2020TimingMeansSameObject → ⊥
late2020TimingDoesNotCreateSameObject ()

candidateArchiveDoesNotCreateVerifiedOriginal : CandidateArchiveMeansVerifiedOriginal → ⊥
candidateArchiveDoesNotCreateVerifiedOriginal ()

record AmyArchiveCorporateSameObjectBoundary : Set where
  constructor amy-archive-corporate-same-object-boundary
  field
    priorAmyAndGenericRoutersReused : Bool
    secAndWaybackQidsAttached : Bool
    secCikAndAccessionAttached : Bool
    secPrimaryCanonicalLinkInspected : Bool
    archiveUrlRetainedAsCandidateCapturedCarrier : Bool
    originalFirstPartyCarrierRemainsUnresolved : Bool
    noDoiManufactured : Bool
    deweySeparatedFromRegulatoryAndArchiveIdentifiers : Bool
    capturedArtifactSeparatedFromOriginalProvenance : Bool
    corporateRoleSeparatedFromScientificValidation : Bool
    temporalTopicAdjacencySeparatedFromSameObjectIdentity : Bool
    firstUnpaidLeafRemainsExactDerivativeIdentity : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open AmyArchiveCorporateSameObjectBoundary public

canonicalAmyArchiveCorporateSameObjectBoundary : AmyArchiveCorporateSameObjectBoundary
canonicalAmyArchiveCorporateSameObjectBoundary =
  amy-archive-corporate-same-object-boundary
    true true true true true true true true true true true true true false
