module DASHI.Culture.AmyEskridgePOAMSSAAAgreementTopologyWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.LayeredKnowledgeReleaseBidiExact as ReleaseCore
import DASHI.Culture.POAMSLayeredReleaseExact as Release
import DASHI.Culture.AmyEskridgePOAMSObjectLineageExact as Lineage
import DASHI.Culture.AmyEskridgePOAMSReviewObjectDisambiguationExact as Review
import DASHI.Culture.AmyEskridgeInstituteDerivativeIdentityDiscriminatorExact as D

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: PRIMARY NASA POAMS SAA TOPOLOGY WELD
--
-- NASA's 31-Dec-2016 active Space Act Agreement register separates three
-- Quantum Machines / MSFC carriers that had previously been compressed in the
-- Amy lane into the parent SAA8-1519855 label:
--
--   SAA8-1519855    Advanced Propulsion Theory and Experimentation
--   SAA8-1519855.1  Advanced Propulsion Theory and Experimentation
--                    POAMS Familiarization
--   SAA8-1519855.2  Advanced Propulsion Theory and Experimental Prototyping
--
-- This is source-specific topology, not a new release ontology. An agreement
-- identifier/date proves an agreement carrier; it does not by itself identify
-- Amy's September-2020 NASA-review object or a DAA release case.
------------------------------------------------------------------------

data POAMSAgreementRole : Set where
  parentTheoryExperimentation : POAMSAgreementRole
  poamsFamiliarization : POAMSAgreementRole
  experimentalPrototyping : POAMSAgreementRole

record POAMSAgreementReceipt : Set where
  constructor poams-agreement-receipt
  field
    identifier : String
    role : POAMSAgreementRole
    title : String
    executionDate : String
    expirationDate : String
    partner : String
    center : String
    agreementType : String
    primarySourceReference : String
    exactAgreementIdentityPaid : Bool
    identifiesAmyReviewObject : Bool
    identifiesNASAReleaseCase : Bool
    identifiesInstituteDerivative : Bool

open POAMSAgreementReceipt public

poamsParentAgreement : POAMSAgreementReceipt
poamsParentAgreement = poams-agreement-receipt
  "SAA8-1519855"
  parentTheoryExperimentation
  "Advanced Propulsion Theory and Experimentation"
  "2015-07-01"
  "2020-07-01"
  "Quantum Machines LLC"
  "MSFC"
  "Reimbursable"
  "NASA List of Active Space Act Agreements as of 2016-12-31; NASA/TM-20205010911"
  true false false false

poamsFamiliarizationAgreement : POAMSAgreementReceipt
poamsFamiliarizationAgreement = poams-agreement-receipt
  "SAA8-1519855.1"
  poamsFamiliarization
  "Advanced Propulsion Theory and Experimentation POAMS Familiarization"
  "2015-07-01"
  "2017-07-01"
  "Quantum Machines LLC"
  "MSFC"
  "Reimbursable"
  "NASA List of Active Space Act Agreements as of 2016-12-31"
  true false false false

poamsExperimentalPrototypingAgreement : POAMSAgreementReceipt
poamsExperimentalPrototypingAgreement = poams-agreement-receipt
  "SAA8-1519855.2"
  experimentalPrototyping
  "Advanced Propulsion Theory and Experimental Prototyping"
  "2016-04-08"
  "2018-04-08"
  "Quantum Machines LLC"
  "MSFC"
  "Reimbursable"
  "NASA List of Active Space Act Agreements as of 2016-12-31, PAM 21453"
  true false false false

------------------------------------------------------------------------
-- Identifier namespaces.
--
-- NTRS records the final memorandum's funding number as
-- MSFC-RMB-QUANTUM-SAA8-1519855-1. The active-agreement register separately
-- uses dotted child-agreement identifiers SAA8-1519855.1 and .2. The textual
-- suffixes are not silently equated: a crosswalk needs a primary carrier.
------------------------------------------------------------------------

data POAMSIdentifierNamespace : Set where
  activeAgreementRegisterNamespace : POAMSIdentifierNamespace
  ntrsFundingNumberNamespace : POAMSIdentifierNamespace

record POAMSIdentifierReceipt : Set where
  constructor poams-identifier-receipt
  field
    identifierText : String
    identifierNamespace : POAMSIdentifierNamespace
    sourceReference : String
    exactIdentifierPaid : Bool
    mappedToSpecificAgreementAnnex : Bool
    identifiesAmyReviewObject : Bool

open POAMSIdentifierReceipt public

ntrsFinalTMFundingNumber : POAMSIdentifierReceipt
ntrsFinalTMFundingNumber = poams-identifier-receipt
  "MSFC-RMB-QUANTUM-SAA8-1519855-1"
  ntrsFundingNumberNamespace
  "NASA NTRS 20205010911 funding metadata"
  true false false

record POAMSIdentifierNamespaceBoundary : Set where
  constructor poams-identifier-namespace-boundary
  field
    ntrsHyphenOneEqualsDottedAnnexOne : Bool
    ntrsHyphenOneEqualsDottedAnnexTwo : Bool
    sharedBaseSAAIdentifierCreatesAnnexCrosswalk : Bool
    primaryCrosswalkMayResolveFundingToAnnex : Bool
    fundingNumberMaySeedVersionAndDeliverableSearch : Bool

open POAMSIdentifierNamespaceBoundary public

canonicalPOAMSIdentifierNamespaceBoundary : POAMSIdentifierNamespaceBoundary
canonicalPOAMSIdentifierNamespaceBoundary =
  poams-identifier-namespace-boundary false false false true true

------------------------------------------------------------------------
-- Source-specific temporal topology.
--
-- The .2 prototyping carrier is active across the 7-Oct-2016 NASA test described
-- by the eventual TM. This sharpens the earlier-study referent into a family of
-- exact programme carriers, but does not make .2 the unnamed object Amy said was
-- under NASA review in September 2020.
------------------------------------------------------------------------

record POAMSAgreementTemporalTopology : Set where
  constructor poams-agreement-temporal-topology
  field
    parentBeginsJuly2015 : Bool
    familiarizationBeginsJuly2015 : Bool
    prototypingBeginsApril2016 : Bool
    october2016TestFallsInsideParent : Bool
    october2016TestFallsInsideFamiliarization : Bool
    october2016TestFallsInsidePrototyping : Bool
    familiarizationEndsJuly2017 : Bool
    prototypingEndsApril2018 : Bool
    parentEndsJuly2020 : Bool
    parentEndsBeforeAmySeptember2020Statement : Bool
    agreementExpiryEqualsPublicReleaseApproval : Bool

open POAMSAgreementTemporalTopology public

canonicalPOAMSAgreementTemporalTopology : POAMSAgreementTemporalTopology
canonicalPOAMSAgreementTemporalTopology =
  poams-agreement-temporal-topology
    true true true
    true true true
    true true true true
    false

------------------------------------------------------------------------
-- Participant / authorship / production-stage topology.
--
-- The final TM describes the 7-Oct-2016 test as involving Richard Eskridge,
-- Michael Nelson and Quantum Machines CEO Chris Milam. The final public TM is
-- authored by Richard H. Eskridge, Michael A. Nelson and Michael P. Schoenfeld.
-- Its report metadata identifies the Propulsion Systems Department,
-- Engineering Directorate as the preparing organization and marks Eskridge as
-- retired. These are useful lineage/version discriminators, not retroactive
-- authorship or same-object receipts.
------------------------------------------------------------------------

data POAMSProductionRole : Set where
  experimentParticipant : POAMSProductionRole
  finalReportAuthor : POAMSProductionRole
  reportPreparingOrganization : POAMSProductionRole

record POAMSProductionReceipt : Set where
  constructor poams-production-receipt
  field
    actorOrOrganization : String
    productionRole : POAMSProductionRole
    temporalCoordinate : String
    sourceReference : String
    exactRolePaid : Bool
    createsEarlierPaperAuthorship : Bool
    identifiesAmyReviewObject : Bool

open POAMSProductionReceipt public

milam2016ExperimentParticipant : POAMSProductionReceipt
milam2016ExperimentParticipant = poams-production-receipt
  "Chris Milam / Quantum Machines"
  experimentParticipant
  "2016-10-07 NASA/MSFC POAMS test"
  "NASA/TM-20205010911 retrospective experiment account"
  true false false

schoenfeldFinalTMReportAuthor : POAMSProductionReceipt
schoenfeldFinalTMReportAuthor = poams-production-receipt
  "Michael P. Schoenfeld"
  finalReportAuthor
  "NASA/TM-20205010911 / M-1531 final report"
  "NASA NTRS 20205010911; final TM title/author metadata"
  true false false

propulsionSystemsReportPreparingOrganization : POAMSProductionReceipt
propulsionSystemsReportPreparingOrganization = poams-production-receipt
  "Propulsion Systems Department, Engineering Directorate"
  reportPreparingOrganization
  "final NASA/TM-20205010911 report-production stage"
  "NASA/TM-20205010911 Standard Form 298 / report metadata"
  true false false

record POAMSProductionBoundary : Set where
  constructor poams-production-boundary
  field
    milam2016ParticipationEquals2016PaperAuthorship : Bool
    schoenfeldFinalAuthorshipProves2016TestParticipation : Bool
    authorListTransitionProvesIntermediatePaperIdentity : Bool
    reportPreparingOrganizationEqualsAmyReviewObject : Bool
    authorRoleTransitionMaySeedDraftHistorySearch : Bool
    preparingOrganizationMaySeedRecordsSearch : Bool

open POAMSProductionBoundary public

canonicalPOAMSProductionBoundary : POAMSProductionBoundary
canonicalPOAMSProductionBoundary =
  poams-production-boundary false false false false true true

------------------------------------------------------------------------
-- Cross-pollination into existing Amy objects.
------------------------------------------------------------------------

reviewStillHasEarlierNASAStudyReferent :
  Review.ReviewReferentCandidate
reviewStillHasEarlierNASAStudyReferent = Review.earlierNASAStudyReferent

studyStillDistinctFromFinalTM :
  Lineage.earlierStudyDistinctFromLaterTM
    Lineage.canonicalCurrentPOAMSLineageAssessment ≡ true
studyStillDistinctFromFinalTM = refl

existingLayeredReleaseStillRequestsSameObjectWeld :
  ReleaseCore.target Release.poamsNeedsDerivativeIdentity ≡
    ReleaseCore.sameLayerSameObjectWeld
existingLayeredReleaseStillRequestsSameObjectWeld = refl

------------------------------------------------------------------------
-- Discriminator consequence.
--
-- SAA8-1519855.2 is a newly explicit primary programme identifier, but the Amy
-- identity consumer asks for an Amy-linked release/review identifier. Therefore
-- .2 is retained as a high-value narrowing receipt, not silently upgraded to a
-- paid primaryNASAReleaseIdentifier.
------------------------------------------------------------------------

prototypingAgreementNarrowsEarlierStudyReferent : D.IdentityDiscriminatorReceipt
prototypingAgreementNarrowsEarlierStudyReferent = D.identity-discriminator-receipt
  D.primaryNASAReleaseIdentifier
  D.retainedLead
  "Primary NASA SAA8-1519855.2: Advanced Propulsion Theory and Experimental Prototyping, 2016-04-08 through 2018-04-08; exact programme carrier overlapping the October-2016 test, but not an Amy-linked September-2020 release/review identifier."
  false

------------------------------------------------------------------------
-- Concrete next acquisitions. These are source-specific unresolved records,
-- not another planning ontology. They all feed the existing same-object weld.
------------------------------------------------------------------------

record POAMSVersionLineageResidual : Set where
  constructor poams-version-lineage-residual
  field
    pam21453DeliverableOrCloseout : String
    prototypingAnnexDeliverable : String
    m1531DraftOrVersionHistory : String
    nasaSTIDAANF1676ReleaseRouting : String
    fundingNumberToAnnexCrosswalk : String
    schoenfeldEntryIntoReportChain : String
    sameObjectConsumer : ReleaseCore.LayeredReleaseAcquisitionTarget

open POAMSVersionLineageResidual public

currentPOAMSVersionLineageResidual : POAMSVersionLineageResidual
currentPOAMSVersionLineageResidual = poams-version-lineage-residual
  "recover PAM 21453 closeout/deliverable records and any attached technical products"
  "recover SAA8-1519855.2 deliverable list, statement of work, amendments, closeout, or manuscript references"
  "recover NASA/TM-20205010911 / M-1531 draft filenames, revision history, STI submission package, or report-number assignment chronology"
  "recover DAA/NF-1676/STI public-release routing tied to 20205010911, M-1531, POAMS, Eskridge/Nelson/Schoenfeld, or SAA8-1519855 family"
  "recover a primary NASA record mapping MSFC-RMB-QUANTUM-SAA8-1519855-1 to a specific dotted SAA annex if such a mapping exists"
  "recover dated authorship/review metadata showing when Michael P. Schoenfeld entered the manuscript/report chain"
  ReleaseCore.sameLayerSameObjectWeld

record POAMSSAAAgreementTopologyBoundary : Set where
  constructor poams-saa-agreement-topology-boundary
  field
    parentEqualsFamiliarizationAnnex : Bool
    parentEqualsPrototypingAnnex : Bool
    prototypingAgreementEquals2016Experiment : Bool
    prototypingAgreementEquals2021TM : Bool
    agreementExpiryEqualsProprietaryPeriodEnd : Bool
    agreementExpiryEqualsDAAApproval : Bool
    exactProgrammeIdentifierMayNarrowReviewReferent : Bool
    exactProgrammeIdentifierAlonePaysAmyReviewIdentity : Bool
    existingSameObjectWeldRemainsCanonicalConsumer : Bool
    agreementTopologyCreatesDeathCausation : Bool

open POAMSSAAAgreementTopologyBoundary public

canonicalPOAMSSAAAgreementTopologyBoundary : POAMSSAAAgreementTopologyBoundary
canonicalPOAMSSAAAgreementTopologyBoundary =
  poams-saa-agreement-topology-boundary
    false false false false false false
    true false true false
