module DASHI.Physics.Closure.W2W3GovernancePolicyHookRequest where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation as W2
import DASHI.Physics.Closure.W2GovernanceSelfIssuanceIntakeRequest as W2Intake
import DASHI.Physics.Closure.W2GovernanceTokenConstructorObstruction as W2Obs
import DASHI.Physics.Closure.W2PromotionAuthorityReceipt as W2Audit
import DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate as W3Gate
import DASHI.Physics.Closure.W3AcceptedEvidenceAuthorityTokenGovernanceObstruction as W3Obs
import DASHI.Physics.Closure.W3AcceptedEvidenceAuthorityTokenIntakeRequest as W3Intake
import DASHI.Physics.Closure.W3AcceptedEvidenceAuthorityTokenReceipt as W3Receipt

------------------------------------------------------------------------
-- W2/W3 governance policy hook request.
--
-- This is the smallest honest typed interface for the landed governance
-- policy in the current repo state.  It consumes the policy and the current
-- W2/W3 evidence surfaces as typed inputs, but it deliberately does not
-- return either constructorless authority token.

data DASHIGovernanceEvidenceClass : Set where
  reflProvedInternalEvidence :
    DASHIGovernanceEvidenceClass
  publicDOIFrozenCommitEvidence :
    DASHIGovernanceEvidenceClass

data W2W3GovernanceHookDisposition : Set where
  policyEvidenceConsumedRequestOnly :
    W2W3GovernanceHookDisposition

data W2W3TokenProducingHookAuthorization : Set where
  tokenProducingHookBlockedByCurrentTypedState :
    W2W3TokenProducingHookAuthorization

record DASHIGovernanceSelfIssuancePolicyEvidence : Setω where
  field
    policyDocument :
      String

    reflProvedInternalSelfIssuanceAllowed :
      Bool

    reflProvedInternalSelfIssuanceAllowedIsTrue :
      reflProvedInternalSelfIssuanceAllowed
      ≡
      true

    publicDOIFrozenCommitSelfIssuanceAllowed :
      Bool

    publicDOIFrozenCommitSelfIssuanceAllowedIsTrue :
      publicDOIFrozenCommitSelfIssuanceAllowed
      ≡
      true

    externalCountersignatureRequiredForOtherClasses :
      Bool

    externalCountersignatureRequiredForOtherClassesIsTrue :
      externalCountersignatureRequiredForOtherClasses
      ≡
      true

    tokensConstructedByThisPolicy :
      Bool

    tokensConstructedByThisPolicyIsFalse :
      tokensConstructedByThisPolicy
      ≡
      false

    requiredSelfIssuanceReceiptFields :
      List String

    revocationConditions :
      List String

    noOverreachClauses :
      List String

canonicalDASHIGovernanceSelfIssuancePolicyEvidence :
  DASHIGovernanceSelfIssuancePolicyEvidence
canonicalDASHIGovernanceSelfIssuancePolicyEvidence =
  record
    { policyDocument =
        "Docs/DASHIGovernanceSelfIssuancePolicy.md"
    ; reflProvedInternalSelfIssuanceAllowed =
        true
    ; reflProvedInternalSelfIssuanceAllowedIsTrue =
        refl
    ; publicDOIFrozenCommitSelfIssuanceAllowed =
        true
    ; publicDOIFrozenCommitSelfIssuanceAllowedIsTrue =
        refl
    ; externalCountersignatureRequiredForOtherClasses =
        true
    ; externalCountersignatureRequiredForOtherClassesIsTrue =
        refl
    ; tokensConstructedByThisPolicy =
        false
    ; tokensConstructedByThisPolicyIsFalse =
        refl
    ; requiredSelfIssuanceReceiptFields =
        "policy"
        ∷ "evidenceClass"
        ∷ "tokenName"
        ∷ "laneScope"
        ∷ "evidencePacket"
        ∷ "frozenCommit when empirical or runner-dependent"
        ∷ "artifactDigests when artifacts are consumed"
        ∷ "publicAuthorityRefs when public evidence is consumed"
        ∷ "comparisonOrProofLaw"
        ∷ "nonCollapseOrNoOverreachWitness"
        ∷ "auditLog"
        ∷ "revocationConditions"
        ∷ []
    ; revocationConditions =
        "public DOI, table id, payload checksum, or artifact digest mismatch"
        ∷ "frozen commit mismatch"
        ∷ "failed reproduction of the stated proof, runner, semantic match, or comparison law"
        ∷ "later accepted external authority rejects the evidence packet"
        ∷ "token used outside its named bounded scope"
        ∷ "non-collapse or no-overreach witness invalidated"
        ∷ "dependency receipt withdrawn, superseded, or found to import an unstated authority assumption"
        ∷ "evidence class misclassified"
        ∷ []
    ; noOverreachClauses =
        "no broad W2 closure beyond the named W2 receipt"
        ∷ "no broad W3 empirical adequacy beyond the named W3 receipt"
        ∷ "no W4/W5 Drell-Yan convention or physical-unit authority"
        ∷ "no W8 origin promotion"
        ∷ "no W9 cancellation pressure promotion"
        ∷ "no G5 empirical adequacy as a whole"
        ∷ "no full physics unification"
        ∷ []
    }

record W2GovernanceHookEvidenceConsumption : Setω where
  field
    policyEvidence :
      DASHIGovernanceSelfIssuancePolicyEvidence

    evidenceClass :
      DASHIGovernanceEvidenceClass

    intakeRequest :
      W2Intake.W2GovernanceSelfIssuanceIntakeRequest

    auditDiagnostic :
      W2Audit.W2PromotionAuthorityAuditDiagnostic

    constructorObstruction :
      W2Obs.W2GovernanceTokenConstructorObstruction

    exactTokenName :
      String

    typedPolicyEvidenceConsumed :
      Bool

    typedPolicyEvidenceConsumedIsTrue :
      typedPolicyEvidenceConsumed
      ≡
      true

    tokenProducingHookAuthorizedNow :
      Bool

    tokenProducingHookAuthorizedNowIsFalse :
      tokenProducingHookAuthorizedNow
      ≡
      false

    authorization :
      W2W3TokenProducingHookAuthorization

    authorityTokenConstructedHere :
      Bool

    authorityTokenConstructedHereIsFalse :
      authorityTokenConstructedHere
      ≡
      false

    authorityTokenUnavailable :
      W2.NaturalP2ConvergencePromotionAuthorityToken →
      ⊥

    remainingPayloadFields :
      List W2.NaturalP2ConvergenceMissingField

    noPromotionBoundary :
      List String

canonicalW2GovernanceHookEvidenceConsumption :
  W2GovernanceHookEvidenceConsumption
canonicalW2GovernanceHookEvidenceConsumption =
  record
    { policyEvidence =
        canonicalDASHIGovernanceSelfIssuancePolicyEvidence
    ; evidenceClass =
        reflProvedInternalEvidence
    ; intakeRequest =
        W2Intake.canonicalW2GovernanceSelfIssuanceIntakeRequest
    ; auditDiagnostic =
        W2Audit.canonicalW2PromotionAuthorityAuditDiagnostic
    ; constructorObstruction =
        W2Obs.canonicalW2GovernanceTokenConstructorObstruction
    ; exactTokenName =
        "NaturalP2ConvergencePromotionAuthorityToken"
    ; typedPolicyEvidenceConsumed =
        true
    ; typedPolicyEvidenceConsumedIsTrue =
        refl
    ; tokenProducingHookAuthorizedNow =
        false
    ; tokenProducingHookAuthorizedNowIsFalse =
        refl
    ; authorization =
        tokenProducingHookBlockedByCurrentTypedState
    ; authorityTokenConstructedHere =
        false
    ; authorityTokenConstructedHereIsFalse =
        refl
    ; authorityTokenUnavailable =
        W2.naturalP2ConvergencePromotionAuthorityUnavailable
    ; remainingPayloadFields =
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
    ; noPromotionBoundary =
        "The policy is consumed as W2 governance evidence"
        ∷ "No NaturalP2ConvergencePromotionAuthorityToken is constructed"
        ∷ "No NaturalP2ConvergencePromotionReceipt is constructed"
        ∷ "Natural/p2 and carrier-general convergence payload receipts remain missing"
        ∷ []
    }

record W3GovernanceHookEvidenceConsumption : Setω where
  field
    policyEvidence :
      DASHIGovernanceSelfIssuancePolicyEvidence

    evidenceClass :
      DASHIGovernanceEvidenceClass

    intakeRequest :
      W3Intake.W3AcceptedEvidenceAuthorityTokenIntakeRequest

    providerResponse :
      W3Receipt.W3AcceptedEvidenceAuthorityProviderResponse

    constructorObstruction :
      W3Obs.W3AcceptedEvidenceAuthorityTokenGovernanceObstruction

    exactTokenName :
      String

    typedPolicyEvidenceConsumed :
      Bool

    typedPolicyEvidenceConsumedIsTrue :
      typedPolicyEvidenceConsumed
      ≡
      true

    intakeSelfIssuancePermitted :
      Bool

    intakeSelfIssuancePermittedIsFalse :
      intakeSelfIssuancePermitted
      ≡
      false

    providerCanonicalTableChecksumBindingPresent :
      Bool

    providerCanonicalTableChecksumBindingPresentIsFalse :
      providerCanonicalTableChecksumBindingPresent
      ≡
      false

    providerResponseContainsAcceptedToken :
      Bool

    providerResponseContainsAcceptedTokenIsFalse :
      providerResponseContainsAcceptedToken
      ≡
      false

    tokenProducingHookAuthorizedNow :
      Bool

    tokenProducingHookAuthorizedNowIsFalse :
      tokenProducingHookAuthorizedNow
      ≡
      false

    authorization :
      W2W3TokenProducingHookAuthorization

    authorityTokenConstructedHere :
      Bool

    authorityTokenConstructedHereIsFalse :
      authorityTokenConstructedHere
      ≡
      false

    authorityTokenUnavailable :
      W3Gate.W3AcceptedEvidenceAuthorityToken →
      ⊥

    noPromotionBoundary :
      List String

canonicalW3GovernanceHookEvidenceConsumption :
  W3GovernanceHookEvidenceConsumption
canonicalW3GovernanceHookEvidenceConsumption =
  record
    { policyEvidence =
        canonicalDASHIGovernanceSelfIssuancePolicyEvidence
    ; evidenceClass =
        publicDOIFrozenCommitEvidence
    ; intakeRequest =
        W3Intake.canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
    ; providerResponse =
        W3Receipt.canonicalW3AcceptedEvidenceAuthorityProviderResponse
    ; constructorObstruction =
        W3Obs.canonicalW3AcceptedEvidenceAuthorityTokenGovernanceObstruction
    ; exactTokenName =
        "W3AcceptedEvidenceAuthorityToken"
    ; typedPolicyEvidenceConsumed =
        true
    ; typedPolicyEvidenceConsumedIsTrue =
        refl
    ; intakeSelfIssuancePermitted =
        W3Intake.W3AcceptedEvidenceAuthorityTokenIntakeRequest.selfIssuancePermitted
          W3Intake.canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
    ; intakeSelfIssuancePermittedIsFalse =
        refl
    ; providerCanonicalTableChecksumBindingPresent =
        W3Receipt.W3AcceptedEvidenceAuthorityProviderResponse.providerCanonicalTableChecksumBindingPresent
          W3Receipt.canonicalW3AcceptedEvidenceAuthorityProviderResponse
    ; providerCanonicalTableChecksumBindingPresentIsFalse =
        refl
    ; providerResponseContainsAcceptedToken =
        W3Receipt.W3AcceptedEvidenceAuthorityProviderResponse.responseContainsAcceptedToken
          W3Receipt.canonicalW3AcceptedEvidenceAuthorityProviderResponse
    ; providerResponseContainsAcceptedTokenIsFalse =
        refl
    ; tokenProducingHookAuthorizedNow =
        false
    ; tokenProducingHookAuthorizedNowIsFalse =
        refl
    ; authorization =
        tokenProducingHookBlockedByCurrentTypedState
    ; authorityTokenConstructedHere =
        false
    ; authorityTokenConstructedHereIsFalse =
        refl
    ; authorityTokenUnavailable =
        W3Obs.w3AcceptedEvidenceAuthorityTokenStillUninhabited
    ; noPromotionBoundary =
        "The policy is consumed as W3 governance evidence"
        ∷ "No W3AcceptedEvidenceAuthorityToken is constructed"
        ∷ "No W3AcceptedEvidenceAuthorityTokenReceipt is constructed"
        ∷ "No W3AcceptedAuthorityExternalReceipt is constructed"
        ∷ "Provider accepted authority response and provider canonical table-checksum binding remain absent"
        ∷ []
    }

record W2W3GovernancePolicyHookRequest : Setω where
  field
    policyEvidence :
      DASHIGovernanceSelfIssuancePolicyEvidence

    w2EvidenceConsumption :
      W2GovernanceHookEvidenceConsumption

    w3EvidenceConsumption :
      W3GovernanceHookEvidenceConsumption

    hookDisposition :
      W2W3GovernanceHookDisposition

    tokenProducingHookAuthorization :
      W2W3TokenProducingHookAuthorization

    typedPolicyEvidenceConsumed :
      Bool

    typedPolicyEvidenceConsumedIsTrue :
      typedPolicyEvidenceConsumed
      ≡
      true

    tokenProducingHookAuthorizedNow :
      Bool

    tokenProducingHookAuthorizedNowIsFalse :
      tokenProducingHookAuthorizedNow
      ≡
      false

    w2Promoted :
      Bool

    w2PromotedIsFalse :
      w2Promoted
      ≡
      false

    w3Promoted :
      Bool

    w3PromotedIsFalse :
      w3Promoted
      ≡
      false

    w2AuthorityTokenUnavailable :
      W2.NaturalP2ConvergencePromotionAuthorityToken →
      ⊥

    w3AuthorityTokenUnavailable :
      W3Gate.W3AcceptedEvidenceAuthorityToken →
      ⊥

    smallestHonestTypedInterface :
      List String

    noPromotionBoundary :
      List String

canonicalW2W3GovernancePolicyHookRequest :
  W2W3GovernancePolicyHookRequest
canonicalW2W3GovernancePolicyHookRequest =
  record
    { policyEvidence =
        canonicalDASHIGovernanceSelfIssuancePolicyEvidence
    ; w2EvidenceConsumption =
        canonicalW2GovernanceHookEvidenceConsumption
    ; w3EvidenceConsumption =
        canonicalW3GovernanceHookEvidenceConsumption
    ; hookDisposition =
        policyEvidenceConsumedRequestOnly
    ; tokenProducingHookAuthorization =
        tokenProducingHookBlockedByCurrentTypedState
    ; typedPolicyEvidenceConsumed =
        true
    ; typedPolicyEvidenceConsumedIsTrue =
        refl
    ; tokenProducingHookAuthorizedNow =
        false
    ; tokenProducingHookAuthorizedNowIsFalse =
        refl
    ; w2Promoted =
        false
    ; w2PromotedIsFalse =
        refl
    ; w3Promoted =
        false
    ; w3PromotedIsFalse =
        refl
    ; w2AuthorityTokenUnavailable =
        W2.naturalP2ConvergencePromotionAuthorityUnavailable
    ; w3AuthorityTokenUnavailable =
        W3Obs.w3AcceptedEvidenceAuthorityTokenStillUninhabited
    ; smallestHonestTypedInterface =
        "Consume Docs/DASHIGovernanceSelfIssuancePolicy.md as typed policy evidence"
        ∷ "Attach the current W2 governance intake, W2 audit, and W2 constructor obstruction"
        ∷ "Attach the current W3 authority-token intake, provider-response skeleton, and W3 constructor obstruction"
        ∷ "Record tokenProducingHookAuthorizedNow = false while the exact authority-token datatypes remain constructorless"
        ∷ "Request a future explicit constructor or non-postulated hook before any token receipt is populated"
        ∷ []
    ; noPromotionBoundary =
        "This aggregate hook is an obstruction/request surface only"
        ∷ "It records policy consumption but constructs no authority token"
        ∷ "W2 remains blocked on authority plus natural/p2 and carrier-general payload receipts"
        ∷ "W3 remains blocked on accepted authority-token response and provider canonical table-checksum binding"
        ∷ "No W2, W3, W4/W5, W8, W9, G5, non-limited-paper, or full-unification promotion follows"
        ∷ []
    }

canonicalW2W3GovernanceHookConsumesPolicy :
  W2W3GovernancePolicyHookRequest.typedPolicyEvidenceConsumed
    canonicalW2W3GovernancePolicyHookRequest
  ≡
  true
canonicalW2W3GovernanceHookConsumesPolicy = refl

canonicalW2W3GovernanceHookDoesNotAuthorizeTokenProduction :
  W2W3GovernancePolicyHookRequest.tokenProducingHookAuthorizedNow
    canonicalW2W3GovernancePolicyHookRequest
  ≡
  false
canonicalW2W3GovernanceHookDoesNotAuthorizeTokenProduction = refl

canonicalW2GovernanceHookRemainsBlocked :
  W2W3GovernancePolicyHookRequest.w2Promoted
    canonicalW2W3GovernancePolicyHookRequest
  ≡
  false
canonicalW2GovernanceHookRemainsBlocked = refl

canonicalW3GovernanceHookRemainsBlocked :
  W2W3GovernancePolicyHookRequest.w3Promoted
    canonicalW2W3GovernancePolicyHookRequest
  ≡
  false
canonicalW3GovernanceHookRemainsBlocked = refl
