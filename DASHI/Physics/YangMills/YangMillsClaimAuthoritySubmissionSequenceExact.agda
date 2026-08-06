module DASHI.Physics.YangMills.YangMillsClaimAuthoritySubmissionSequenceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Clay Mathematics Institute,
-- "Rules for the Millennium Prize Problems", revised rules adopted
-- 26 September 2018.  URL: claymath.org/millennium-problems/rules/.
-- No DOI assigned.
--
-- External claim snapshot, accessed 2026-08-06:
-- Oliver Odusanya, "Yang-Mills Mass Gap -- Constructive Proof",
-- yangmills.dev.  Self-hosted website; no qualifying-outlet or CMI-recognition
-- status is asserted by this module.  The page's theorem and verification
-- claims are recorded only as claims requiring independent mathematical audit.
--
-- DASHI CONTRIBUTION
--
-- Encode the Clay procedure as a strict sequential state machine.  A
-- self-hosted theorem claim, a machine-verification claim and a refereed
-- qualifying publication are distinct evidence kinds.  None can be coerced
-- into the next.  This prevents procedural status from being inferred from
-- confidence, page count, implementation language or a named proof engine.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

data PublicationEvidence : Set where
  selfHostedWebClaim : PublicationEvidence
  downloadablePreprint : PublicationEvidence
  machineVerificationArtifact : PublicationEvidence
  qualifyingRefereedPublication : PublicationEvidence
  twoYearsElapsedEvidence : PublicationEvidence
  globalAcceptanceEvidence : PublicationEvidence
  CMIReviewDecision : PublicationEvidence

data ClayProcedureStage : Set where
  privateDraftStage : ClayProcedureStage
  publicClaimStage : ClayProcedureStage
  qualifyingOutletStage : ClayProcedureStage
  twoYearWaitingStage : ClayProcedureStage
  generalAcceptanceStage : ClayProcedureStage
  CMIConsiderationStage : ClayProcedureStage

nextProcedureStage : ClayProcedureStage → ClayProcedureStage
nextProcedureStage privateDraftStage = publicClaimStage
nextProcedureStage publicClaimStage = qualifyingOutletStage
nextProcedureStage qualifyingOutletStage = twoYearWaitingStage
nextProcedureStage twoYearWaitingStage = generalAcceptanceStage
nextProcedureStage generalAcceptanceStage = CMIConsiderationStage
nextProcedureStage CMIConsiderationStage = CMIConsiderationStage

advancesStage : PublicationEvidence → ClayProcedureStage → Bool
advancesStage selfHostedWebClaim privateDraftStage = true
advancesStage downloadablePreprint privateDraftStage = true
advancesStage machineVerificationArtifact privateDraftStage = false
advancesStage qualifyingRefereedPublication publicClaimStage = true
advancesStage twoYearsElapsedEvidence qualifyingOutletStage = true
advancesStage globalAcceptanceEvidence twoYearWaitingStage = true
advancesStage CMIReviewDecision generalAcceptanceStage = true
advancesStage _ _ = false

selfHostedClaimDoesNotAdvanceToQualifyingOutlet :
  advancesStage selfHostedWebClaim publicClaimStage ≡ false
selfHostedClaimDoesNotAdvanceToQualifyingOutlet = refl

machineArtifactDoesNotAdvanceToQualifyingOutlet :
  advancesStage machineVerificationArtifact publicClaimStage ≡ false
machineArtifactDoesNotAdvanceToQualifyingOutlet = refl

qualifyingPublicationAdvancesOnlyFirstClayGate :
  advancesStage qualifyingRefereedPublication publicClaimStage ≡ true
qualifyingPublicationAdvancesOnlyFirstClayGate = refl

twoYearEvidenceNeededAfterPublication :
  advancesStage twoYearsElapsedEvidence qualifyingOutletStage ≡ true
twoYearEvidenceNeededAfterPublication = refl

globalAcceptanceNeededAfterWaiting :
  advancesStage globalAcceptanceEvidence twoYearWaitingStage ≡ true
globalAcceptanceNeededAfterWaiting = refl

selfHostedIsNotQualifyingPublication :
  selfHostedWebClaim ≡ qualifyingRefereedPublication → ⊥
selfHostedIsNotQualifyingPublication ()

machineArtifactIsNotGlobalAcceptance :
  machineVerificationArtifact ≡ globalAcceptanceEvidence → ⊥
machineArtifactIsNotGlobalAcceptance ()

data AuditStatus : Set where
  observedClaim : AuditStatus
  notEstablishedByCurrentAudit : AuditStatus
  independentlyEstablished : AuditStatus

record ExternalClaimAudit : Set where
  constructor externalClaimAudit
  field
    channel : PublicationEvidence
    theoremContentStatus : AuditStatus
    proofArtifactReproducibilityStatus : AuditStatus
    qualifyingOutletStatus : AuditStatus
    globalAcceptanceStatus : AuditStatus

currentYangMillsDevAudit : ExternalClaimAudit
currentYangMillsDevAudit =
  externalClaimAudit
    selfHostedWebClaim
    notEstablishedByCurrentAudit
    notEstablishedByCurrentAudit
    notEstablishedByCurrentAudit
    notEstablishedByCurrentAudit

record ClaimAuthorityBoundary : Set where
  constructor claimAuthorityBoundary
  field
    pageCountImpliesCorrectness : Set
    pageCountDoesNotImplyCorrectness : pageCountImpliesCorrectness → Set

    multipleImplementationLanguagesImplyPeerReview : Set
    implementationLanguagesDoNotImplyPeerReview :
      multipleImplementationLanguagesImplyPeerReview → Set

canonicalClaimAuthorityBoundary : ClaimAuthorityBoundary
canonicalClaimAuthorityBoundary =
  claimAuthorityBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
