module DASHI.Physics.Closure.W2GovernanceSelfIssuanceIntakeRequest where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation as W2
import DASHI.Physics.Closure.W2PromotionAuthorityReceipt as W2Audit
import DASHI.Physics.Closure.W2W3SelfIssuanceGovernanceRulingDiagnostic as Ruling

------------------------------------------------------------------------
-- W2 governance self-issuance intake request.
--
-- This is the narrow W2 closing packet for the current promotion authority
-- token boundary.  The landed normalizeAdd sum-invariance and local uniform
-- rate surface are accepted as W2 evidence, but current governance still keeps
-- `NaturalP2ConvergencePromotionAuthorityToken` constructorless.  Therefore
-- this module requests governance action and records closure as blocked; it
-- does not self-issue a token or construct a promotion receipt.

data W2GovernanceSelfIssuanceIntakeDisposition : Set where
  w2SelfIssuanceIntakeReadyButGovernanceBlocked :
    W2GovernanceSelfIssuanceIntakeDisposition

data W2GovernanceRequestedAction : Set where
  explicitNaturalP2PromotionAuthorityPolicyHookRequired :
    W2GovernanceRequestedAction

record W2GovernanceSelfIssuanceIntakeRequest : Setω where
  field
    w2Audit :
      W2Audit.W2PromotionAuthorityAuditDiagnostic

    w2CurrentStatus :
      W2.NaturalP2ConvergencePromotionCurrentStatus

    governanceRulingDiagnostic :
      Ruling.W2W3SelfIssuanceGovernanceRulingDiagnostic

    intakeDisposition :
      W2GovernanceSelfIssuanceIntakeDisposition

    requestedAction :
      W2GovernanceRequestedAction

    selfIssuanceAvailable :
      Bool

    selfIssuanceAvailableIsFalse :
      selfIssuanceAvailable ≡ false

    authorityTokenUnavailable :
      W2.NaturalP2ConvergencePromotionAuthorityToken → ⊥

    promotionReceiptImpossible :
      W2.NaturalP2ConvergencePromotionReceipt → ⊥

    exactBlockingFields :
      List W2.NaturalP2ConvergenceMissingField

    governanceIntakePacket :
      List String

    closingPacket :
      List String

canonicalW2GovernanceSelfIssuanceIntakeRequest :
  W2GovernanceSelfIssuanceIntakeRequest
canonicalW2GovernanceSelfIssuanceIntakeRequest =
  record
    { w2Audit =
        W2Audit.canonicalW2PromotionAuthorityAuditDiagnostic
    ; w2CurrentStatus =
        W2.currentNaturalP2ConvergencePromotionStatus
    ; governanceRulingDiagnostic =
        Ruling.canonicalW2W3SelfIssuanceGovernanceRulingDiagnostic
    ; intakeDisposition =
        w2SelfIssuanceIntakeReadyButGovernanceBlocked
    ; requestedAction =
        explicitNaturalP2PromotionAuthorityPolicyHookRequired
    ; selfIssuanceAvailable =
        false
    ; selfIssuanceAvailableIsFalse =
        refl
    ; authorityTokenUnavailable =
        W2.naturalP2ConvergencePromotionAuthorityUnavailable
    ; promotionReceiptImpossible =
        W2.naturalP2ConvergencePromotionReceiptImpossible
    ; exactBlockingFields =
        W2Audit.W2PromotionAuthorityAuditDiagnostic.remainingTypedFields
          W2Audit.canonicalW2PromotionAuthorityAuditDiagnostic
    ; governanceIntakePacket =
        "Governance intake: W2 normalizeAdd sum/p-adic invariance and local uniform rate support are landed evidence"
        ∷ "Exact blocker: NaturalP2ConvergencePromotionAuthorityToken is constructorless under current governance"
        ∷ "Required governance action: identify an explicit NaturalP2ConvergencePromotionAuthorityToken constructor or existing policy hook, plus the evidence payload it certifies"
        ∷ "A prose self-issuance ruling is insufficient while the token datatype remains constructorless"
        ∷ []
    ; closingPacket =
        "Closing packet: W2 is not promoted by this request"
        ∷ "No NaturalP2ConvergencePromotionAuthorityToken is constructed here"
        ∷ "No NaturalP2ConvergencePromotionReceipt is constructed here"
        ∷ "Current state remains governance-blocked pending explicit promotion authority policy"
        ∷ []
    }

canonicalW2GovernanceSelfIssuanceUnavailable :
  W2GovernanceSelfIssuanceIntakeRequest.selfIssuanceAvailable
    canonicalW2GovernanceSelfIssuanceIntakeRequest
    ≡
  false
canonicalW2GovernanceSelfIssuanceUnavailable = refl
