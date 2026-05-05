module DASHI.Physics.Closure.W2W3SelfIssuanceGovernanceRulingDiagnostic where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation as W2
import DASHI.Physics.Closure.W2PromotionAuthorityReceipt as W2Audit
import DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate as W3Gate
import DASHI.Physics.Closure.W3AcceptedEvidenceAuthorityTokenIntakeRequest as W3Intake

------------------------------------------------------------------------
-- W2/W3 self-issuance governance ruling diagnostic.
--
-- This audits the proposed single governance ruling for W2/W3 token
-- self-issuance against the current repo policy.  The policy is still the
-- constructorless-token policy: local evidence surfaces may be recorded, but
-- they do not self-issue NaturalP2ConvergencePromotionAuthorityToken or
-- W3AcceptedEvidenceAuthorityToken.

data W2W3SelfIssuancePolicyStatus : Set where
  selfIssuanceForbiddenByConstructorlessAuthorityTokens :
    W2W3SelfIssuancePolicyStatus

data W2W3SingleRulingEffect : Set where
  noStatusChangeWithoutExplicitConstructorPolicyChange :
    W2W3SingleRulingEffect

data W2W3RequiredGovernanceRuling : Set where
  explicitSelfIssuanceConstructorPolicyForW2AndW3Required :
    W2W3RequiredGovernanceRuling

data W2CurrentGovernanceStatus : Set where
  w2BlockedAwaitingNaturalP2PromotionAuthorityToken :
    W2CurrentGovernanceStatus

data W3CurrentGovernanceStatus : Set where
  w3BlockedAwaitingAcceptedEvidenceAuthorityToken :
    W3CurrentGovernanceStatus

w3AcceptedEvidenceAuthorityTokenUnavailable :
  W3Gate.W3AcceptedEvidenceAuthorityToken → ⊥
w3AcceptedEvidenceAuthorityTokenUnavailable ()

record W2W3SelfIssuanceGovernanceRulingDiagnostic : Setω where
  field
    policyStatus :
      W2W3SelfIssuancePolicyStatus

    proposedSingleRulingEffect :
      W2W3SingleRulingEffect

    exactRequiredRuling :
      W2W3RequiredGovernanceRuling

    w2Audit :
      W2Audit.W2PromotionAuthorityAuditDiagnostic

    w2CurrentStatus :
      W2.NaturalP2ConvergencePromotionCurrentStatus

    w2Status :
      W2CurrentGovernanceStatus

    w2SelfIssuanceAvailable :
      Bool

    w2SelfIssuanceAvailableIsFalse :
      w2SelfIssuanceAvailable ≡ false

    w2AuthorityTokenStillUninhabited :
      W2.NaturalP2ConvergencePromotionAuthorityToken → ⊥

    w2PromotionReceiptStillImpossible :
      W2.NaturalP2ConvergencePromotionReceipt → ⊥

    w3TokenIntake :
      W3Intake.W3AcceptedEvidenceAuthorityTokenIntakeRequest

    w3Status :
      W3CurrentGovernanceStatus

    w3SelfIssuanceAvailable :
      Bool

    w3SelfIssuanceAvailableIsFalse :
      w3SelfIssuanceAvailable ≡ false

    w3AuthorityTokenStillUninhabited :
      W3Gate.W3AcceptedEvidenceAuthorityToken → ⊥

    rulingRequiredToChangeStatus :
      List String

    authorityBoundary :
      List String

canonicalW2W3SelfIssuanceGovernanceRulingDiagnostic :
  W2W3SelfIssuanceGovernanceRulingDiagnostic
canonicalW2W3SelfIssuanceGovernanceRulingDiagnostic =
  record
    { policyStatus =
        selfIssuanceForbiddenByConstructorlessAuthorityTokens
    ; proposedSingleRulingEffect =
        noStatusChangeWithoutExplicitConstructorPolicyChange
    ; exactRequiredRuling =
        explicitSelfIssuanceConstructorPolicyForW2AndW3Required
    ; w2Audit =
        W2Audit.canonicalW2PromotionAuthorityAuditDiagnostic
    ; w2CurrentStatus =
        W2.currentNaturalP2ConvergencePromotionStatus
    ; w2Status =
        w2BlockedAwaitingNaturalP2PromotionAuthorityToken
    ; w2SelfIssuanceAvailable =
        false
    ; w2SelfIssuanceAvailableIsFalse =
        refl
    ; w2AuthorityTokenStillUninhabited =
        W2.naturalP2ConvergencePromotionAuthorityUnavailable
    ; w2PromotionReceiptStillImpossible =
        W2.naturalP2ConvergencePromotionReceiptImpossible
    ; w3TokenIntake =
        W3Intake.canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
    ; w3Status =
        w3BlockedAwaitingAcceptedEvidenceAuthorityToken
    ; w3SelfIssuanceAvailable =
        false
    ; w3SelfIssuanceAvailableIsFalse =
        refl
    ; w3AuthorityTokenStillUninhabited =
        w3AcceptedEvidenceAuthorityTokenUnavailable
    ; rulingRequiredToChangeStatus =
        "A status-changing ruling must explicitly amend the constructorless-token policy for both NaturalP2ConvergencePromotionAuthorityToken and W3AcceptedEvidenceAuthorityToken"
        ∷ "The ruling must identify the self-issuance constructor or governance hook and the evidence payload each token is allowed to certify"
        ∷ "A prose statement that W2/W3 may self-issue is insufficient while both token datatypes remain constructorless"
        ∷ []
    ; authorityBoundary =
        "No NaturalP2ConvergencePromotionAuthorityToken is constructed here"
        ∷ "No NaturalP2ConvergencePromotionReceipt is constructed here"
        ∷ "No W3AcceptedEvidenceAuthorityToken is constructed here"
        ∷ "W2 local normalizeAdd and uniform-rate support remains evidence, not promotion authority"
        ∷ "W3 bounded t43 comparison and runner evidence remains evidence, not accepted-authority token issuance"
        ∷ []
    }

canonicalW2W3SelfIssuancePolicyStatus :
  W2W3SelfIssuanceGovernanceRulingDiagnostic.policyStatus
    canonicalW2W3SelfIssuanceGovernanceRulingDiagnostic
    ≡
  selfIssuanceForbiddenByConstructorlessAuthorityTokens
canonicalW2W3SelfIssuancePolicyStatus = refl

canonicalW2SelfIssuanceStillUnavailable :
  W2W3SelfIssuanceGovernanceRulingDiagnostic.w2SelfIssuanceAvailable
    canonicalW2W3SelfIssuanceGovernanceRulingDiagnostic
    ≡
  false
canonicalW2SelfIssuanceStillUnavailable = refl

canonicalW3SelfIssuanceStillUnavailable :
  W2W3SelfIssuanceGovernanceRulingDiagnostic.w3SelfIssuanceAvailable
    canonicalW2W3SelfIssuanceGovernanceRulingDiagnostic
    ≡
  false
canonicalW3SelfIssuanceStillUnavailable = refl
