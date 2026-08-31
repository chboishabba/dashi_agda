module DASHI.Biology.EducationAuditDecisionNoncollapseExact where

open import DASHI.Core.Prelude

import DASHI.Reasoning.ClaimAuditManifestExact as Manifest
import DASHI.Cognition.PNF.BoundedEvidenceCommitmentExact as DecisionEvidence
import DASHI.Cognition.PNF.DecisionConfidenceNoncollapseExact as Confidence

------------------------------------------------------------------------
-- STRUCTURAL CROSS-POLLINATION ONLY
--
-- The cognition owners prove finite type distinctions:
--   accumulated evidence != commitment
--   confidence != commitment.
--
-- This education-governance adapter reuses only those non-collapse patterns.
-- It does not treat the cited decision-neuroscience papers as empirical evidence
-- about AERO, ACPUE or the Teaching and Learning Commission.
------------------------------------------------------------------------

data AuditEvidenceState : Set where
  auditRegistered
  boundedSupportAccumulated
  independentAuditCompleted
  reproducedBoundedFinding : AuditEvidenceState

data AuditConfidence : Set where
  confidenceUnreported
  lowAuditConfidence
  moderateAuditConfidence
  highAuditConfidence : AuditConfidence

data PolicyCommitment : Set where
  noPolicyCommitment
  recommendationForReview
  authorisedPolicyPromotion : PolicyCommitment

data PolicyAuthorityReceipt : Set where
  authorityReceipt : PolicyAuthorityReceipt

record EducationAuditDecisionState : Set where
  constructor educationAuditDecisionState
  field
    evidenceState : AuditEvidenceState
    confidence : AuditConfidence
    manifestStage : Manifest.AuditStage
    policyCommitment : PolicyCommitment
    authorityReceiptPresent : Bool

open EducationAuditDecisionState public

replicatedButNotPromoted : EducationAuditDecisionState
replicatedButNotPromoted =
  educationAuditDecisionState
    reproducedBoundedFinding
    highAuditConfidence
    Manifest.independentlyReproduced
    noPolicyCommitment
    false

sameEvidenceDifferentCommitmentA : EducationAuditDecisionState
sameEvidenceDifferentCommitmentA =
  educationAuditDecisionState
    independentAuditCompleted
    moderateAuditConfidence
    Manifest.dualCoded
    noPolicyCommitment
    false

sameEvidenceDifferentCommitmentB : EducationAuditDecisionState
sameEvidenceDifferentCommitmentB =
  educationAuditDecisionState
    independentAuditCompleted
    moderateAuditConfidence
    Manifest.dualCoded
    recommendationForReview
    false

sameEvidenceState :
  evidenceState sameEvidenceDifferentCommitmentA ≡
  evidenceState sameEvidenceDifferentCommitmentB
sameEvidenceState = refl

sameConfidenceState :
  confidence sameEvidenceDifferentCommitmentA ≡
  confidence sameEvidenceDifferentCommitmentB
sameConfidenceState = refl

sameManifestStage :
  manifestStage sameEvidenceDifferentCommitmentA ≡
  manifestStage sameEvidenceDifferentCommitmentB
sameManifestStage = refl

sameEvidenceDoesNotDetermineCommitment :
  policyCommitment sameEvidenceDifferentCommitmentA ≡
  policyCommitment sameEvidenceDifferentCommitmentB → ⊥
sameEvidenceDoesNotDetermineCommitment ()

------------------------------------------------------------------------
-- Authorised promotion is separately gated.  The witness is intentionally
-- minimal: possessing a strong audit result is not itself the authority token.
------------------------------------------------------------------------

data MayAuthorisePolicyPromotion :
    EducationAuditDecisionState → Set where
  mayAuthorise :
    {state : EducationAuditDecisionState} →
    policyCommitment state ≡ authorisedPolicyPromotion →
    authorityReceiptPresent state ≡ true →
    PolicyAuthorityReceipt →
    MayAuthorisePolicyPromotion state

replicatedFindingAloneDoesNotAuthorise :
  ¬ MayAuthorisePolicyPromotion replicatedButNotPromoted
replicatedFindingAloneDoesNotAuthorise ()

------------------------------------------------------------------------
-- Regression pointers to the source structural distinctions.
------------------------------------------------------------------------

cognitionEvidenceAccumulationStillNotCommitment :
  DecisionEvidence.contextGate DecisionEvidence.attendEvidence DecisionEvidence.e0
    ≡ DecisionEvidence.e1
  × DecisionEvidence.threshold DecisionEvidence.e1
    ≡ DecisionEvidence.stillDeliberating
cognitionEvidenceAccumulationStillNotCommitment =
  DecisionEvidence.accumulationIsNotCommitment

cognitionConfidenceStillNotCommitment :
  Confidence.commitment Confidence.committedLowConfidence ≡
  Confidence.commitment Confidence.committedHighConfidence
cognitionConfidenceStillNotCommitment =
  Confidence.sameCommitmentDifferentConfidence

record EducationAuditDecisionBoundary : Set where
  constructor educationAuditDecisionBoundary
  field
    auditEvidenceEqualsPolicyCommitment : Bool
    highConfidenceEqualsPolicyAuthority : Bool
    independentReproductionEqualsPolicyActuation : Bool
    recommendationForReviewEqualsAuthorisedPolicy : Bool
    policyAuthorityRequiresSeparateReceipt : Bool
    cognitionSourcesEmpiricallyEstablishCommissionGovernance : Bool

canonicalEducationAuditDecisionBoundary : EducationAuditDecisionBoundary
canonicalEducationAuditDecisionBoundary =
  educationAuditDecisionBoundary false false false false true false
