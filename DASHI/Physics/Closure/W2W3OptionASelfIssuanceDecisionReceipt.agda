module DASHI.Physics.Closure.W2W3OptionASelfIssuanceDecisionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation as W2
import DASHI.Arithmetic.UniformConvergenceRateSurface as W2Rate
import DASHI.Physics.Closure.W2W3GovernancePolicyHookRequest as Hook
import DASHI.Physics.Closure.W2W3TokenProducingHooks as TokenHooks
import DASHI.Physics.Closure.W2W3SelfIssuanceGovernanceRulingDiagnostic as Ruling
import DASHI.Physics.Closure.W3AcceptedEvidenceAuthorityTokenIntakeRequest as W3Intake
import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptRequestPack as W3Pack
import DASHI.Physics.Closure.W3CanonicalChecksumBindingReceipt as W3Checksum

------------------------------------------------------------------------
-- W2/W3 Option-A self-issuance decision receipt.
--
-- This records the current governance decision surface after the formalism
-- asserts that W2/W3 should be self-certifiable under Option A.  It is
-- deliberately fail-closed: the policy permits the evidence classes, but the
-- current typed repo still has no token-producing constructor or hook for the
-- exact W2 and W3 authority token result types.

data W2W3OptionASelfIssuanceDecisionStatus : Set where
  optionARequestedButFailClosedUnderCurrentTypedPolicy :
    W2W3OptionASelfIssuanceDecisionStatus
  optionAAuthorizedButFailClosedUntilExactTokenHooksExist :
    W2W3OptionASelfIssuanceDecisionStatus

data W2W3OptionAOwnerDecisionRequired : Set where
  explicitTokenProducingHookOrConstructorDecisionRequired :
    W2W3OptionAOwnerDecisionRequired

data W2W3OptionAOwnerDecision : Set where
  optionAAuthorizeExactTokenProducingHooks :
    W2W3OptionAOwnerDecision
  optionARejectKeepExternalCountersignatureRequired :
    W2W3OptionAOwnerDecision
  optionADecisionPending :
    W2W3OptionAOwnerDecision

data W2W3OptionAPolicyRequestStatus : Set where
  OptionARequestedButNotAuthorized :
    W2W3OptionAPolicyRequestStatus
  OptionAAuthorizedButExactTokenProducingHooksMissing :
    W2W3OptionAPolicyRequestStatus

data W2W3CurrentSelfIssuanceVerdict : Set where
  cannotSelfIssueExactTokensUnderCurrentPolicy :
    W2W3CurrentSelfIssuanceVerdict
  optionAAuthorizedButCannotSelfIssueUntilTokenHooksExist :
    W2W3CurrentSelfIssuanceVerdict

data W2W3OptionAExactRemainingBlocker : Set where
  missingW2TokenProducingHook :
    W2W3OptionAExactRemainingBlocker
  missingW3TokenProducingHook :
    W2W3OptionAExactRemainingBlocker
  missingW2NonAuthorityPayloadPackaging :
    W2W3OptionAExactRemainingBlocker

record W2W3OptionAPolicyRequestSurface : Setω where
  field
    requestStatus :
      W2W3OptionAPolicyRequestStatus

    ownerDecision :
      W2W3OptionAOwnerDecision

    ownerDecisionIsAuthorized :
      ownerDecision
      ≡
      optionAAuthorizeExactTokenProducingHooks

    externalClaim :
      Bool

    externalClaimIsFalse :
      externalClaim
      ≡
      false

    internalClaim :
      Bool

    internalClaimIsTrue :
      internalClaim
      ≡
      true

    scopeBounded :
      Bool

    scopeBoundedIsTrue :
      scopeBounded
      ≡
      true

    policyEvidence :
      Hook.DASHIGovernanceSelfIssuancePolicyEvidence

    hookRequest :
      Hook.W2W3GovernancePolicyHookRequest

    constructorAuthorizationDiagnostic :
      Hook.W2W3PolicyConstructorAuthorizationDiagnostic

    tokenProducingHookRequestSurface :
      TokenHooks.W2W3TokenProducingHookRequestSurface

    tokenProducingHookRequestSurfaceConstructsNoTokens :
      TokenHooks.W2W3TokenProducingHookRequestSurface.constructsAuthorityTokens
        tokenProducingHookRequestSurface
      ≡
      false

    w2UniformRateEvidence :
      W2Rate.UniformNormalizeAddRateDiagnostic

    w2EvidenceClassPermitted :
      Bool

    w2EvidenceClassPermittedIsTrue :
      w2EvidenceClassPermitted
      ≡
      true

    w2ExactMissingField :
      W2.NaturalP2ConvergenceMissingField

    w2ExactMissingFieldIsAuthorityToken :
      w2ExactMissingField
      ≡
      W2.missingPromotionAuthorityToken

    w2AuthorityTokenConstructed :
      Bool

    w2AuthorityTokenConstructedIsFalse :
      w2AuthorityTokenConstructed
      ≡
      false

    w3ChecksumBindingReceipt :
      W3Checksum.W3CanonicalChecksumBindingReceipt

    w3ChecksumEvidenceReady :
      Bool

    w3ChecksumEvidenceReadyIsTrue :
      w3ChecksumEvidenceReady
      ≡
      true

    w3ProviderCanonicalBindingPresent :
      Bool

    w3ProviderCanonicalBindingPresentIsTrue :
      w3ProviderCanonicalBindingPresent
      ≡
      true

    w3ChecksumBindingDoesNotConstructAuthorityToken :
      W3Checksum.W3CanonicalChecksumBindingReceipt.constructsW3AcceptedEvidenceAuthorityToken
        w3ChecksumBindingReceipt
      ≡
      false

    w3ExactMissingProviderField :
      W3Pack.W3AcceptedAuthorityProviderMissingField

    w3ExactMissingProviderFieldIsAuthorityToken :
      w3ExactMissingProviderField
      ≡
      W3Pack.missingAcceptedEvidenceAuthorityToken

    w3AuthorityTokenConstructed :
      Bool

    w3AuthorityTokenConstructedIsFalse :
      w3AuthorityTokenConstructed
      ≡
      false

    tokenProducingHookAuthorizedNow :
      Bool

    tokenProducingHookAuthorizedNowIsFalse :
      tokenProducingHookAuthorizedNow
      ≡
      false

    exactRemainingBlockers :
      List W2W3OptionAExactRemainingBlocker

    yesNoDecisionRequired :
      List String

    noPromotionBoundary :
      List String

record W2W3OptionASelfIssuanceDecisionReceipt : Setω where
  field
    policyEvidence :
      Hook.DASHIGovernanceSelfIssuancePolicyEvidence

    rulingDiagnostic :
      Ruling.W2W3SelfIssuanceGovernanceRulingDiagnostic

    hookRequest :
      Hook.W2W3GovernancePolicyHookRequest

    constructorAuthorizationDiagnostic :
      Hook.W2W3PolicyConstructorAuthorizationDiagnostic

    tokenProducingHookRequestSurface :
      TokenHooks.W2W3TokenProducingHookRequestSurface

    tokenProducingHookRequestSurfaceConstructsNoTokens :
      TokenHooks.W2W3TokenProducingHookRequestSurface.constructsAuthorityTokens
        tokenProducingHookRequestSurface
      ≡
      false

    formalismRequestsOptionA :
      Bool

    formalismRequestsOptionAIsTrue :
      formalismRequestsOptionA
      ≡
      true

    currentSelfIssuanceVerdict :
      W2W3CurrentSelfIssuanceVerdict

    canSelfIssueExactTokensNow :
      Bool

    canSelfIssueExactTokensNowIsFalse :
      canSelfIssueExactTokensNow
      ≡
      false

    optionAImplementedNow :
      Bool

    optionAImplementedNowIsFalse :
      optionAImplementedNow
      ≡
      false

    selfIssuanceReady :
      Bool

    selfIssuanceReadyIsFalse :
      selfIssuanceReady
      ≡
      false

    decisionStatus :
      W2W3OptionASelfIssuanceDecisionStatus

    ownerDecisionRequired :
      W2W3OptionAOwnerDecisionRequired

    tokenProducingHookAuthorizedNow :
      Bool

    tokenProducingHookAuthorizedNowIsFalse :
      tokenProducingHookAuthorizedNow
      ≡
      false

    w2LocalUniformRateEvidence :
      W2Rate.UniformNormalizeAddRateDiagnostic

    w2NormalizeAddSurfaceFixed :
      W2Rate.UniformNormalizeAddRateDiagnostic.State
        w2LocalUniformRateEvidence
      ≡
      W2Rate.UniformNormalizeAddRateDiagnostic.State
        W2Rate.canonicalUniformNormalizeAddRateDiagnostic

    w2NormalizeAddRateDoesNotConstructAuthority :
      W2Rate.UniformNormalizeAddRateDiagnostic.noW2PromotionAuthorityConstructed
        w2LocalUniformRateEvidence
      ≡
      W2Rate.UniformNormalizeAddRateDiagnostic.noW2PromotionAuthorityConstructed
        W2Rate.canonicalUniformNormalizeAddRateDiagnostic

    w2ClosedByThisReceipt :
      Bool

    w2ClosedByThisReceiptIsFalse :
      w2ClosedByThisReceipt
      ≡
      false

    w3ClosedByThisReceipt :
      Bool

    w3ClosedByThisReceiptIsFalse :
      w3ClosedByThisReceipt
      ≡
      false

    w2ExactMissingField :
      W2.NaturalP2ConvergenceMissingField

    w2ExactMissingFieldIsAuthorityToken :
      w2ExactMissingField
      ≡
      W2.missingPromotionAuthorityToken

    w2NonAuthorityPayloadStillMissing :
      List W2.NaturalP2ConvergenceMissingField

    w3IntakeRequest :
      W3Intake.W3AcceptedEvidenceAuthorityTokenIntakeRequest

    w3PacketReadyForAuthority :
      Bool

    w3PacketReadyForAuthorityIsTrue :
      w3PacketReadyForAuthority
      ≡
      true

    w3IntakeSelfIssuancePermitted :
      Bool

    w3IntakeSelfIssuancePermittedIsFalse :
      w3IntakeSelfIssuancePermitted
      ≡
      false

    w3CanonicalTableChecksumBound :
      Bool

    w3CanonicalTableChecksumBoundIsFalse :
      w3CanonicalTableChecksumBound
      ≡
      false

    w3ProviderCanonicalBindingPresent :
      Bool

    w3ProviderCanonicalBindingPresentIsFalse :
      w3ProviderCanonicalBindingPresent
      ≡
      false

    w3ChecksumBindingReceipt :
      W3Checksum.W3CanonicalChecksumBindingReceipt

    w3NonGovernanceTableChecksumBound :
      Bool

    w3NonGovernanceTableChecksumBoundIsTrue :
      w3NonGovernanceTableChecksumBound
      ≡
      true

    w3NonGovernanceProviderCanonicalBindingPresent :
      Bool

    w3NonGovernanceProviderCanonicalBindingPresentIsTrue :
      w3NonGovernanceProviderCanonicalBindingPresent
      ≡
      true

    w3ChecksumBindingDoesNotConstructAuthorityToken :
      W3Checksum.W3CanonicalChecksumBindingReceipt.constructsW3AcceptedEvidenceAuthorityToken
        w3ChecksumBindingReceipt
      ≡
      false

    w3ExactMissingProviderField :
      W3Pack.W3AcceptedAuthorityProviderMissingField

    w3ExactMissingProviderFieldIsAuthorityToken :
      w3ExactMissingProviderField
      ≡
      W3Pack.missingAcceptedEvidenceAuthorityToken

    minimalTypedPolicyChangeRequired :
      List String

    noPromotionBoundary :
      List String

canonicalW2W3OptionASelfIssuanceDecisionReceipt :
  W2W3OptionASelfIssuanceDecisionReceipt
canonicalW2W3OptionASelfIssuanceDecisionReceipt =
  record
    { policyEvidence =
        Hook.canonicalDASHIGovernanceSelfIssuancePolicyEvidence
    ; rulingDiagnostic =
        Ruling.canonicalW2W3SelfIssuanceGovernanceRulingDiagnostic
    ; hookRequest =
        Hook.canonicalW2W3GovernancePolicyHookRequest
    ; constructorAuthorizationDiagnostic =
        Hook.canonicalW2W3PolicyConstructorAuthorizationDiagnostic
    ; tokenProducingHookRequestSurface =
        TokenHooks.canonicalW2W3TokenProducingHookRequestSurface
    ; tokenProducingHookRequestSurfaceConstructsNoTokens =
        TokenHooks.canonicalW2W3HookSurfaceConstructsNoAuthorityTokens
    ; formalismRequestsOptionA =
        true
    ; formalismRequestsOptionAIsTrue =
        refl
    ; currentSelfIssuanceVerdict =
        optionAAuthorizedButCannotSelfIssueUntilTokenHooksExist
    ; canSelfIssueExactTokensNow =
        false
    ; canSelfIssueExactTokensNowIsFalse =
        refl
    ; optionAImplementedNow =
        false
    ; optionAImplementedNowIsFalse =
        refl
    ; selfIssuanceReady =
        false
    ; selfIssuanceReadyIsFalse =
        refl
    ; decisionStatus =
        optionAAuthorizedButFailClosedUntilExactTokenHooksExist
    ; ownerDecisionRequired =
        explicitTokenProducingHookOrConstructorDecisionRequired
    ; tokenProducingHookAuthorizedNow =
        Hook.W2W3GovernancePolicyHookRequest.tokenProducingHookAuthorizedNow
          Hook.canonicalW2W3GovernancePolicyHookRequest
    ; tokenProducingHookAuthorizedNowIsFalse =
        refl
    ; w2LocalUniformRateEvidence =
        W2Rate.canonicalUniformNormalizeAddRateDiagnostic
    ; w2NormalizeAddSurfaceFixed =
        refl
    ; w2NormalizeAddRateDoesNotConstructAuthority =
        refl
    ; w2ClosedByThisReceipt =
        false
    ; w2ClosedByThisReceiptIsFalse =
        refl
    ; w3ClosedByThisReceipt =
        false
    ; w3ClosedByThisReceiptIsFalse =
        refl
    ; w2ExactMissingField =
        Hook.W2W3PolicyConstructorAuthorizationDiagnostic.w2ExactFirstMissingField
          Hook.canonicalW2W3PolicyConstructorAuthorizationDiagnostic
    ; w2ExactMissingFieldIsAuthorityToken =
        Hook.canonicalW2ExactFirstMissingIsAuthorityToken
    ; w2NonAuthorityPayloadStillMissing =
        W2.missingNaturalBridgeOrObstruction
        ∷ W2.missingNaturalityCarrier
        ∷ W2.missingP2SingleStepCarrier
        ∷ W2.missingP2DoubleStepCarrier
        ∷ W2.missingP2NaturalityLaw
        ∷ W2.missingP2CoherenceLaw
        ∷ W2.missingCarrierTransportLaw
        ∷ W2.missingTransportPreservesConvergenceLaw
        ∷ W2.missingCarrierGeneralConvergenceRate
        ∷ W2.missingRealizationUniformityLaw
        ∷ W2.missingUniformRealizationRateBeyondShiftFlow
        ∷ W2.missingOfflineL2ToCarrierRateLift
        ∷ []
    ; w3IntakeRequest =
        W3Intake.canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
    ; w3PacketReadyForAuthority =
        W3Intake.W3AcceptedEvidenceAuthorityTokenIntakeRequest.packetReadyForExternalAuthority
          W3Intake.canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
    ; w3PacketReadyForAuthorityIsTrue =
        W3Intake.canonicalW3AcceptedEvidenceAuthorityTokenPacketReady
    ; w3IntakeSelfIssuancePermitted =
        W3Intake.W3AcceptedEvidenceAuthorityTokenIntakeRequest.selfIssuancePermitted
          W3Intake.canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
    ; w3IntakeSelfIssuancePermittedIsFalse =
        W3Intake.canonicalW3AcceptedEvidenceAuthorityTokenSelfIssuancePermitted
    ; w3CanonicalTableChecksumBound =
        W3Intake.W3AcceptedEvidenceAuthorityTokenIntakeRequest.tableChecksumBound
          W3Intake.canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
    ; w3CanonicalTableChecksumBoundIsFalse =
        W3Intake.canonicalW3AcceptedEvidenceAuthorityTokenTableChecksumBound
    ; w3ProviderCanonicalBindingPresent =
        W3Intake.W3AcceptedEvidenceAuthorityTokenIntakeRequest.providerCanonicalTableChecksumBindingPresent
          W3Intake.canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
    ; w3ProviderCanonicalBindingPresentIsFalse =
        W3Intake.canonicalW3AcceptedEvidenceAuthorityTokenProviderCanonicalBindingAbsent
    ; w3ChecksumBindingReceipt =
        W3Checksum.canonicalW3CanonicalChecksumBindingReceipt
    ; w3NonGovernanceTableChecksumBound =
        W3Checksum.W3CanonicalChecksumBindingReceipt.localTableChecksumBound
          W3Checksum.canonicalW3CanonicalChecksumBindingReceipt
    ; w3NonGovernanceTableChecksumBoundIsTrue =
        W3Checksum.canonicalW3LocalTableChecksumBound
    ; w3NonGovernanceProviderCanonicalBindingPresent =
        W3Checksum.W3CanonicalChecksumBindingReceipt.providerCanonicalTableChecksumBindingPresent
          W3Checksum.canonicalW3CanonicalChecksumBindingReceipt
    ; w3NonGovernanceProviderCanonicalBindingPresentIsTrue =
        W3Checksum.canonicalW3ProviderCanonicalBindingPresent
    ; w3ChecksumBindingDoesNotConstructAuthorityToken =
        W3Checksum.canonicalW3ChecksumBindingDoesNotConstructAuthorityToken
    ; w3ExactMissingProviderField =
        Hook.W2W3PolicyConstructorAuthorizationDiagnostic.w3ExactFirstMissingProviderField
          Hook.canonicalW2W3PolicyConstructorAuthorizationDiagnostic
    ; w3ExactMissingProviderFieldIsAuthorityToken =
        Hook.canonicalW3ExactFirstMissingIsAuthorityToken
    ; minimalTypedPolicyChangeRequired =
        "Add a non-postulated token-producing policy hook whose result type is exactly NaturalP2ConvergencePromotionAuthorityToken, or add an explicit constructor to that datatype"
        ∷ "Add a non-postulated token-producing policy hook whose result type is exactly W3AcceptedEvidenceAuthorityToken, or add an explicit constructor to that datatype"
        ∷ "For W2, the NormalizeAddState/local uniform-rate fork is resolved positively, but authority and carrier-general natural/p2 payload fields still need typed receipt packaging"
        ∷ "For W3, the public evidence packet is ready for authority review; the historical intake still records tableChecksumBound=false and providerCanonicalTableChecksumBindingPresent=false, while W3CanonicalChecksumBindingReceipt now binds the local t43/t44 CSV artifacts and staged canonical HEPData JSON payloads"
        ∷ "The W2 hook must name the bounded W2 evidence payload, audit clauses, revocation clauses, and no-overreach clauses"
        ∷ "The W3 hook must name the public DOI/frozen-commit evidence payload, table checksums or equivalent canonical bindings, comparison law, non-collapse witness, audit clauses, revocation clauses, and no-overreach clauses"
        ∷ "After those hooks exist, downstream receipt fields may consume the tokens; until then Option A remains requested but not implemented"
        ∷ []
    ; noPromotionBoundary =
        "This receipt records the Option-A governance request and exact first missing typed hooks"
        ∷ "It does not construct NaturalP2ConvergencePromotionAuthorityToken"
        ∷ "It does not construct NaturalP2ConvergencePromotionReceipt"
        ∷ "It does not construct W3AcceptedEvidenceAuthorityToken"
        ∷ "It does not construct W3AcceptedAuthorityExternalReceipt"
        ∷ "W2 and W3 remain governance-blocked, not closed"
        ∷ []
    }

canonicalW2W3OptionAPolicyRequestSurface :
  W2W3OptionAPolicyRequestSurface
canonicalW2W3OptionAPolicyRequestSurface =
  record
    { requestStatus =
        OptionAAuthorizedButExactTokenProducingHooksMissing
    ; ownerDecision =
        optionAAuthorizeExactTokenProducingHooks
    ; ownerDecisionIsAuthorized =
        refl
    ; externalClaim =
        false
    ; externalClaimIsFalse =
        refl
    ; internalClaim =
        true
    ; internalClaimIsTrue =
        refl
    ; scopeBounded =
        true
    ; scopeBoundedIsTrue =
        refl
    ; policyEvidence =
        Hook.canonicalDASHIGovernanceSelfIssuancePolicyEvidence
    ; hookRequest =
        Hook.canonicalW2W3GovernancePolicyHookRequest
    ; constructorAuthorizationDiagnostic =
        Hook.canonicalW2W3PolicyConstructorAuthorizationDiagnostic
    ; tokenProducingHookRequestSurface =
        TokenHooks.canonicalW2W3TokenProducingHookRequestSurface
    ; tokenProducingHookRequestSurfaceConstructsNoTokens =
        TokenHooks.canonicalW2W3HookSurfaceConstructsNoAuthorityTokens
    ; w2UniformRateEvidence =
        W2Rate.canonicalUniformNormalizeAddRateDiagnostic
    ; w2EvidenceClassPermitted =
        Hook.W2W3PolicyConstructorAuthorizationDiagnostic.evidenceClassesPermitted
          Hook.canonicalW2W3PolicyConstructorAuthorizationDiagnostic
    ; w2EvidenceClassPermittedIsTrue =
        Hook.W2W3PolicyConstructorAuthorizationDiagnostic.evidenceClassesPermittedIsTrue
          Hook.canonicalW2W3PolicyConstructorAuthorizationDiagnostic
    ; w2ExactMissingField =
        Hook.W2W3PolicyConstructorAuthorizationDiagnostic.w2ExactFirstMissingField
          Hook.canonicalW2W3PolicyConstructorAuthorizationDiagnostic
    ; w2ExactMissingFieldIsAuthorityToken =
        Hook.canonicalW2ExactFirstMissingIsAuthorityToken
    ; w2AuthorityTokenConstructed =
        false
    ; w2AuthorityTokenConstructedIsFalse =
        refl
    ; w3ChecksumBindingReceipt =
        W3Checksum.canonicalW3CanonicalChecksumBindingReceipt
    ; w3ChecksumEvidenceReady =
        W3Checksum.W3CanonicalChecksumBindingReceipt.evidenceReadyForAuthorityReview
          W3Checksum.canonicalW3CanonicalChecksumBindingReceipt
    ; w3ChecksumEvidenceReadyIsTrue =
        W3Checksum.W3CanonicalChecksumBindingReceipt.evidenceReadyForAuthorityReviewIsTrue
          W3Checksum.canonicalW3CanonicalChecksumBindingReceipt
    ; w3ProviderCanonicalBindingPresent =
        W3Checksum.W3CanonicalChecksumBindingReceipt.providerCanonicalTableChecksumBindingPresent
          W3Checksum.canonicalW3CanonicalChecksumBindingReceipt
    ; w3ProviderCanonicalBindingPresentIsTrue =
        W3Checksum.canonicalW3ProviderCanonicalBindingPresent
    ; w3ChecksumBindingDoesNotConstructAuthorityToken =
        W3Checksum.canonicalW3ChecksumBindingDoesNotConstructAuthorityToken
    ; w3ExactMissingProviderField =
        Hook.W2W3PolicyConstructorAuthorizationDiagnostic.w3ExactFirstMissingProviderField
          Hook.canonicalW2W3PolicyConstructorAuthorizationDiagnostic
    ; w3ExactMissingProviderFieldIsAuthorityToken =
        Hook.canonicalW3ExactFirstMissingIsAuthorityToken
    ; w3AuthorityTokenConstructed =
        false
    ; w3AuthorityTokenConstructedIsFalse =
        refl
    ; tokenProducingHookAuthorizedNow =
        Hook.W2W3PolicyConstructorAuthorizationDiagnostic.tokenProducingHookAuthorizedNow
          Hook.canonicalW2W3PolicyConstructorAuthorizationDiagnostic
    ; tokenProducingHookAuthorizedNowIsFalse =
        Hook.canonicalW2W3PolicyDoesNotAuthorizeTokenProduction
    ; exactRemainingBlockers =
        missingW2TokenProducingHook
        ∷ missingW3TokenProducingHook
        ∷ missingW2NonAuthorityPayloadPackaging
        ∷ []
    ; yesNoDecisionRequired =
        "DECIDED YES: Option A is authorized as an internal, bounded self-issuance policy for the exact W2/W3 lanes named here"
        ∷ "IMPLEMENTATION BLOCKER: the exact token-producing hooks or constructors are still absent, so no authority token may be constructed by this receipt"
        ∷ "REJECTION BRANCH RETAINED: if governance later revokes Option A, revert to external countersignature required under the revocation clauses"
        ∷ []
    ; noPromotionBoundary =
        "Option A is authorized only as an internal bounded governance decision"
        ∷ "externalClaim = false; internalClaim = true; scopeBounded = true"
        ∷ "The authorization does not create an external authority and does not fabricate constructorless tokens"
        ∷ "The W3 t43/t44 local CSV and canonical JSON checksum evidence is bound by W3CanonicalChecksumBindingReceipt"
        ∷ "The W2 uniform-rate evidence is present as UniformNormalizeAddRateDiagnostic"
        ∷ "No NaturalP2ConvergencePromotionAuthorityToken is constructed"
        ∷ "No W3AcceptedEvidenceAuthorityToken is constructed"
        ∷ "W2 exact remaining blocker: missing non-postulated token-producing hook for NaturalP2ConvergencePromotionAuthorityToken, plus non-authority payload packaging"
        ∷ "W3 exact remaining blocker: missing non-postulated token-producing hook for W3AcceptedEvidenceAuthorityToken"
        ∷ "No W2 or W3 gate promotion follows until the exact hooks exist and are consumed by downstream receipts"
        ∷ []
    }

canonicalW2W3OptionARequested :
  W2W3OptionASelfIssuanceDecisionReceipt.formalismRequestsOptionA
    canonicalW2W3OptionASelfIssuanceDecisionReceipt
  ≡
  true
canonicalW2W3OptionARequested = refl

canonicalW2W3OptionANotImplementedYet :
  W2W3OptionASelfIssuanceDecisionReceipt.optionAImplementedNow
    canonicalW2W3OptionASelfIssuanceDecisionReceipt
  ≡
  false
canonicalW2W3OptionANotImplementedYet = refl

canonicalW2W3OptionAStillGovernanceBlocked :
  W2W3OptionASelfIssuanceDecisionReceipt.selfIssuanceReady
    canonicalW2W3OptionASelfIssuanceDecisionReceipt
  ≡
  false
canonicalW2W3OptionAStillGovernanceBlocked = refl

canonicalW2W3OptionACannotSelfIssueExactTokensNow :
  W2W3OptionASelfIssuanceDecisionReceipt.canSelfIssueExactTokensNow
    canonicalW2W3OptionASelfIssuanceDecisionReceipt
  ≡
  false
canonicalW2W3OptionACannotSelfIssueExactTokensNow = refl

canonicalW2LocalUniformRateEvidenceIsLandedButNonPromoting :
  W2W3OptionASelfIssuanceDecisionReceipt.w2NormalizeAddRateDoesNotConstructAuthority
    canonicalW2W3OptionASelfIssuanceDecisionReceipt
  ≡
  refl
canonicalW2LocalUniformRateEvidenceIsLandedButNonPromoting = refl

canonicalW3OptionAPacketReadyButSelfIssuanceStillFalse :
  W2W3OptionASelfIssuanceDecisionReceipt.w3IntakeSelfIssuancePermitted
    canonicalW2W3OptionASelfIssuanceDecisionReceipt
  ≡
  false
canonicalW3OptionAPacketReadyButSelfIssuanceStillFalse = refl

canonicalW2W3OptionAPolicyRequestDecisionAuthorized :
  W2W3OptionAPolicyRequestSurface.ownerDecision
    canonicalW2W3OptionAPolicyRequestSurface
  ≡
  optionAAuthorizeExactTokenProducingHooks
canonicalW2W3OptionAPolicyRequestDecisionAuthorized = refl

canonicalW2W3OptionAPolicyRequestDoesNotAuthorizeTokenProduction :
  W2W3OptionAPolicyRequestSurface.tokenProducingHookAuthorizedNow
    canonicalW2W3OptionAPolicyRequestSurface
  ≡
  false
canonicalW2W3OptionAPolicyRequestDoesNotAuthorizeTokenProduction = refl

canonicalW2W3OptionAPolicyRequestBindsW3ChecksumEvidence :
  W2W3OptionAPolicyRequestSurface.w3ChecksumEvidenceReady
    canonicalW2W3OptionAPolicyRequestSurface
  ≡
  true
canonicalW2W3OptionAPolicyRequestBindsW3ChecksumEvidence = refl

canonicalW2W3OptionAExternalClaimFalse :
  W2W3OptionAPolicyRequestSurface.externalClaim
    canonicalW2W3OptionAPolicyRequestSurface
  ≡
  false
canonicalW2W3OptionAExternalClaimFalse = refl

canonicalW2W3OptionAInternalClaimTrue :
  W2W3OptionAPolicyRequestSurface.internalClaim
    canonicalW2W3OptionAPolicyRequestSurface
  ≡
  true
canonicalW2W3OptionAInternalClaimTrue = refl

canonicalW2W3OptionAScopeBoundedTrue :
  W2W3OptionAPolicyRequestSurface.scopeBounded
    canonicalW2W3OptionAPolicyRequestSurface
  ≡
  true
canonicalW2W3OptionAScopeBoundedTrue = refl
