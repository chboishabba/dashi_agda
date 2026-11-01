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
-- NASA STI / DAA process topology contemporaneous with the POAMS manuscript.
--
-- NPR 2200.2C states that the DAA is NASA's compliance review for publication,
-- dissemination and presentation of STI, and that approval is documented on
-- NF-1676 (or the Center implementation). Appendix E states that report
-- production may continue before DAA approval, but a report is not released
-- without an approved DAA; the Center Technical Publications Office / STI
-- Manager reviews manuscript conformance and produces the final copy.
--
-- This is exactly the kind of process Amy described in September 2020, but
-- process-shape compatibility is still not same-object identity.
------------------------------------------------------------------------

data NASASTIReleaseStage : Set where
  manuscriptProduction : NASASTIReleaseStage
  technicalManagementEditorialReview : NASASTIReleaseStage
  nf1676DAAReview : NASASTIReleaseStage
  approvedForRelease : NASASTIReleaseStage
  finalCopyProduction : NASASTIReleaseStage
  externalDissemination : NASASTIReleaseStage

record NASASTIProcessReceipt : Set where
  constructor nasa-sti-process-receipt
  field
    stage : NASASTIReleaseStage
    controllingSource : String
    boundedRule : String
    processRulePaid : Bool
    poamsSpecificArtifactRecovered : Bool
    identifiesAmyReviewObject : Bool

open NASASTIProcessReceipt public

nf1676DAAProcessReceipt : NASASTIProcessReceipt
nf1676DAAProcessReceipt = nasa-sti-process-receipt
  nf1676DAAReview
  "NASA NPR 2200.2C section 4.5 and Appendix E; NF-1676 DAA"
  "DAA review controls publication/dissemination availability and records restrictions; approval is documented on NF-1676 or its Center implementation."
  true false false

preApprovalProductionReceipt : NASASTIProcessReceipt
preApprovalProductionReceipt = nasa-sti-process-receipt
  manuscriptProduction
  "NASA NPR 2200.2C Appendix E.1.7.2"
  "Report production may continue before DAA submission/approval, but the report is not released without an approved DAA."
  true false false

finalCopyProductionReceipt : NASASTIProcessReceipt
finalCopyProductionReceipt = nasa-sti-process-receipt
  finalCopyProduction
  "NASA NPR 2200.2C Appendix E.1.8"
  "The Center Technical Publications Office or STI Manager ensures manuscript conformance and recommends/incorporates final changes to produce the final copy."
  true false false

record AmyPOAMSDAAProcessFit : Set where
  constructor amy-poams-daa-process-fit
  field
    amyDescribedNASAReviewReleaseDependency : Bool
    nasaProcessAllowsProductionBeforeDAAApproval : Bool
    nasaProcessRequiresApprovalBeforeRelease : Bool
    nasaProcessHasFinalCopyStageAfterManuscriptReview : Bool
    ntrsAcquisitionAfterAmyStatement : Bool
    processShapeCompatibleWithAmyStatement : Bool
    processShapeDeterminesSameObject : Bool
    ntrsAcquisitionEqualsDAAApprovalDate : Bool
    publicTMContainsItsNF1676Identifier : Bool

open AmyPOAMSDAAProcessFit public

canonicalAmyPOAMSDAAProcessFit : AmyPOAMSDAAProcessFit
canonicalAmyPOAMSDAAProcessFit = amy-poams-daa-process-fit
  true true true true true true false false false

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
------------------------------------------------------------------------

prototypingAgreementNarrowsEarlierStudyReferent : D.IdentityDiscriminatorReceipt
prototypingAgreementNarrowsEarlierStudyReferent = D.identity-discriminator-receipt
  D.primaryNASAReleaseIdentifier
  D.retainedLead
  "Primary NASA SAA8-1519855.2: Advanced Propulsion Theory and Experimental Prototyping, 2016-04-08 through 2018-04-08; exact programme carrier overlapping the October-2016 test, but not an Amy-linked September-2020 release/review identifier."
  false

nf1676IsNowTheExactReleaseArtifactClass : D.IdentityDiscriminatorReceipt
nf1676IsNowTheExactReleaseArtifactClass = D.identity-discriminator-receipt
  D.primaryNASAReleaseIdentifier
  D.retainedLead
  "NASA policy identifies NF-1676 / Center DAA implementation as the approval artifact class for external NASA STI release. The POAMS-specific NF-1676/DAA remains unrecovered, so the discriminator is narrowed but unpaid."
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
  "recover the POAMS-specific NF-1676 / Center DAA record and its associated manuscript identity, approval routing, restrictions, approval date and release disposition"
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
