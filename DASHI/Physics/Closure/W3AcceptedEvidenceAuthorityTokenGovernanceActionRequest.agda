module DASHI.Physics.Closure.W3AcceptedEvidenceAuthorityTokenGovernanceActionRequest where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Set; Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataW3NonCollapseWitnessReceipt as NonCollapse
import DASHI.Physics.Closure.W2W3GovernancePolicyHookRequest as Hook
import DASHI.Physics.Closure.W2W3TokenProducingHooks as TokenHooks
import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptObligation as EXT
import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptRequestPack as Pack
import DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate as AUTH
import DASHI.Physics.Closure.W3AcceptedEvidenceAuthorityTokenGovernanceObstruction as Obs
import DASHI.Physics.Closure.W3AcceptedEvidenceAuthorityTokenIntakeRequest as Intake
import DASHI.Physics.Closure.W3AcceptedEvidenceAuthorityTokenReceipt as Receipt
import DASHI.Physics.Closure.W3CanonicalChecksumBindingReceipt as Checksum

------------------------------------------------------------------------
-- W3 accepted-evidence authority token governance-action request.
--
-- This is a W3-only request/diagnostic surface.  It deliberately does not add
-- a constructor to W3AcceptedEvidenceAuthorityToken.  The exact constructor or
-- exact non-postulated hook for that token is treated as a future governance
-- action, because adding either one changes which evidence is allowed to issue
-- the W3 accepted-authority token.

data W3AcceptedEvidenceAuthorityTokenGovernanceAction : Set where
  addExactConstructorAtCanonicalDefinitionSite :
    W3AcceptedEvidenceAuthorityTokenGovernanceAction
  addExactNonPostulatedPolicyHookAtCanonicalBoundary :
    W3AcceptedEvidenceAuthorityTokenGovernanceAction

data W3AcceptedEvidenceAuthorityTokenGovernanceActionStatus : Set where
  governanceActionRequiredAndNotPresentInCurrentRepo :
    W3AcceptedEvidenceAuthorityTokenGovernanceActionStatus

data W3SelfIssuanceFeasibilityVerdict : Set where
  feasibleOnlyAfterExplicitGovernanceAction :
    W3SelfIssuanceFeasibilityVerdict

data W3AcceptedEvidenceAuthorityTokenDownstreamBlocker : Set where
  missingProviderAcceptedEvidenceAuthorityToken :
    W3AcceptedEvidenceAuthorityTokenDownstreamBlocker
  missingProviderCanonicalTableChecksumBinding :
    W3AcceptedEvidenceAuthorityTokenDownstreamBlocker
  missingW3AcceptedAuthorityExternalReceipt :
    W3AcceptedEvidenceAuthorityTokenDownstreamBlocker
  missingW3EvidenceBackedEmpiricalTarget :
    W3AcceptedEvidenceAuthorityTokenDownstreamBlocker
  missingB4EmpiricalPromotion :
    W3AcceptedEvidenceAuthorityTokenDownstreamBlocker
  missingOriginReceiptPromotion :
    W3AcceptedEvidenceAuthorityTokenDownstreamBlocker
  missingW4W5AcceptedDYLuminosityConvention :
    W3AcceptedEvidenceAuthorityTokenDownstreamBlocker
  missingFullEmpiricalPromotionBoundaryReview :
    W3AcceptedEvidenceAuthorityTokenDownstreamBlocker

record W3AcceptedEvidenceAuthorityTokenGovernanceActionRequest : Setω where
  field
    policyEvidence :
      Hook.DASHIGovernanceSelfIssuancePolicyEvidence

    governanceHookEvidenceConsumption :
      Hook.W3GovernanceHookEvidenceConsumption

    tokenProducingHookRequest :
      TokenHooks.W3TokenProducingHookRequest

    constructorObstruction :
      Obs.W3AcceptedEvidenceAuthorityTokenGovernanceObstruction

    definitionSiteClosure :
      AUTH.W3AcceptedEvidenceAuthorityTokenDefinitionSiteClosure

    definitionSiteAudit :
      AUTH.W3AcceptedEvidenceAuthorityTokenDefinitionSiteAudit

    intakeRequest :
      Intake.W3AcceptedEvidenceAuthorityTokenIntakeRequest

    providerResponse :
      Receipt.W3AcceptedEvidenceAuthorityProviderResponse

    currentExternalStatus :
      EXT.W3AcceptedAuthorityExternalReceiptCurrentStatus

    checksumBindingReceipt :
      Checksum.W3CanonicalChecksumBindingReceipt

    runnerNonCollapseReceipt :
      NonCollapse.HEPDataW3T43RunnerPerBinNonCollapseReceipt

    requestedResultType :
      Set

    requestedResultTypeIsExactW3AuthorityToken :
      requestedResultType
      ≡
      AUTH.W3AcceptedEvidenceAuthorityToken

    governanceActionStatus :
      W3AcceptedEvidenceAuthorityTokenGovernanceActionStatus

    selfIssuanceFeasibility :
      W3SelfIssuanceFeasibilityVerdict

    exactGovernanceActions :
      List W3AcceptedEvidenceAuthorityTokenGovernanceAction

    exactConstructorGovernanceAction :
      String

    exactHookGovernanceAction :
      String

    governanceActionRequired :
      Bool

    governanceActionRequiredIsTrue :
      governanceActionRequired
      ≡
      true

    exactConstructorOrHookPresentNow :
      Bool

    exactConstructorOrHookPresentNowIsFalse :
      exactConstructorOrHookPresentNow
      ≡
      false

    acceptedNonPostulatedExactPolicyHookPresent :
      Bool

    acceptedNonPostulatedExactPolicyHookPresentIsFalse :
      acceptedNonPostulatedExactPolicyHookPresent
      ≡
      false

    authorityTokenConstructedHere :
      Bool

    authorityTokenConstructedHereIsFalse :
      authorityTokenConstructedHere
      ≡
      false

    tokenUnavailable :
      AUTH.W3AcceptedEvidenceAuthorityToken →
      ⊥

    providerAcceptedTokenPresent :
      Bool

    providerAcceptedTokenPresentIsFalse :
      providerAcceptedTokenPresent
      ≡
      false

    providerCanonicalTableChecksumBindingPresent :
      Bool

    providerCanonicalTableChecksumBindingPresentIsFalse :
      providerCanonicalTableChecksumBindingPresent
      ≡
      false

    localCanonicalChecksumBound :
      Bool

    localCanonicalChecksumBoundIsTrue :
      localCanonicalChecksumBound
      ≡
      true

    remainingDownstreamBlockers :
      List W3AcceptedEvidenceAuthorityTokenDownstreamBlocker

    remainingDownstreamBlockerDescriptions :
      List String

    requiredGovernancePayload :
      List String

    noPromotionBoundary :
      List String

canonicalW3AcceptedEvidenceAuthorityTokenGovernanceActionRequest :
  W3AcceptedEvidenceAuthorityTokenGovernanceActionRequest
canonicalW3AcceptedEvidenceAuthorityTokenGovernanceActionRequest =
  record
    { policyEvidence =
        Hook.canonicalDASHIGovernanceSelfIssuancePolicyEvidence
    ; governanceHookEvidenceConsumption =
        Hook.canonicalW3GovernanceHookEvidenceConsumption
    ; tokenProducingHookRequest =
        TokenHooks.canonicalW3TokenProducingHookRequest
    ; constructorObstruction =
        Obs.canonicalW3AcceptedEvidenceAuthorityTokenGovernanceObstruction
    ; definitionSiteClosure =
        AUTH.canonicalW3AcceptedEvidenceAuthorityTokenDefinitionSiteClosure
    ; definitionSiteAudit =
        AUTH.canonicalW3AcceptedEvidenceAuthorityTokenDefinitionSiteAudit
    ; intakeRequest =
        Intake.canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
    ; providerResponse =
        Receipt.canonicalW3AcceptedEvidenceAuthorityProviderResponse
    ; currentExternalStatus =
        EXT.currentW3AcceptedAuthorityExternalReceiptStatus
    ; checksumBindingReceipt =
        Checksum.canonicalW3CanonicalChecksumBindingReceipt
    ; runnerNonCollapseReceipt =
        NonCollapse.canonicalHEPDataW3T43RunnerPerBinNonCollapseReceipt
    ; requestedResultType =
        AUTH.W3AcceptedEvidenceAuthorityToken
    ; requestedResultTypeIsExactW3AuthorityToken =
        refl
    ; governanceActionStatus =
        governanceActionRequiredAndNotPresentInCurrentRepo
    ; selfIssuanceFeasibility =
        feasibleOnlyAfterExplicitGovernanceAction
    ; exactGovernanceActions =
        addExactConstructorAtCanonicalDefinitionSite
        ∷ addExactNonPostulatedPolicyHookAtCanonicalBoundary
        ∷ []
    ; exactConstructorGovernanceAction =
        "Governance action: add an accepted constructor to DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3AcceptedEvidenceAuthorityToken"
    ; exactHookGovernanceAction =
        "Governance action: add a non-postulated exact policy hook whose result type is W3AcceptedEvidenceAuthorityToken at the canonical authority boundary"
    ; governanceActionRequired =
        true
    ; governanceActionRequiredIsTrue =
        refl
    ; exactConstructorOrHookPresentNow =
        false
    ; exactConstructorOrHookPresentNowIsFalse =
        refl
    ; acceptedNonPostulatedExactPolicyHookPresent =
        false
    ; acceptedNonPostulatedExactPolicyHookPresentIsFalse =
        refl
    ; authorityTokenConstructedHere =
        false
    ; authorityTokenConstructedHereIsFalse =
        refl
    ; tokenUnavailable =
        Obs.w3AcceptedEvidenceAuthorityTokenStillUninhabited
    ; providerAcceptedTokenPresent =
        TokenHooks.W3TokenProducingPolicyHookRequiredSignature.providerAcceptedTokenPresent
          TokenHooks.canonicalW3TokenProducingPolicyHookRequiredSignature
    ; providerAcceptedTokenPresentIsFalse =
        refl
    ; providerCanonicalTableChecksumBindingPresent =
        Receipt.W3AcceptedEvidenceAuthorityProviderResponse.providerCanonicalTableChecksumBindingPresent
          Receipt.canonicalW3AcceptedEvidenceAuthorityProviderResponse
    ; providerCanonicalTableChecksumBindingPresentIsFalse =
        refl
    ; localCanonicalChecksumBound =
        Checksum.W3CanonicalChecksumBindingReceipt.localTableChecksumBound
          Checksum.canonicalW3CanonicalChecksumBindingReceipt
    ; localCanonicalChecksumBoundIsTrue =
        refl
    ; remainingDownstreamBlockers =
        missingProviderAcceptedEvidenceAuthorityToken
        ∷ missingProviderCanonicalTableChecksumBinding
        ∷ missingW3AcceptedAuthorityExternalReceipt
        ∷ missingW3EvidenceBackedEmpiricalTarget
        ∷ missingB4EmpiricalPromotion
        ∷ missingOriginReceiptPromotion
        ∷ missingW4W5AcceptedDYLuminosityConvention
        ∷ missingFullEmpiricalPromotionBoundaryReview
        ∷ []
    ; remainingDownstreamBlockerDescriptions =
        "Provider response still lacks the accepted W3 evidence-authority token"
        ∷ "Provider-side canonical t43/t44 table checksum or equivalent binding is still absent"
        ∷ "W3AcceptedAuthorityExternalReceipt.authorityToken remains uninhabited"
        ∷ "W3EvidenceBackedEmpiricalTarget cannot be assembled without W3AcceptedEvidenceAuthorityToken"
        ∷ "B4 empirical promotion remains a separate downstream blocker"
        ∷ "Origin receipt promotion remains a separate downstream blocker"
        ∷ "W4/W5 accepted DY luminosity convention remains separate and is not supplied by W3 self-issuance"
        ∷ "A final empirical-promotion boundary review is still required before any broad W3 promotion claim"
        ∷ []
    ; requiredGovernancePayload =
        "policy evidence: Docs/DASHIGovernanceSelfIssuancePolicy.md"
        ∷ "evidence class: publicDOIFrozenCommitEvidence"
        ∷ "exact result type: W3AcceptedEvidenceAuthorityToken"
        ∷ "canonical t43/t44 checksum binding and frozen commit"
        ∷ "candidate comparison law and chi2-per-dof payload"
        ∷ "HEPDataW3T43RunnerPerBinNonCollapseReceipt"
        ∷ "audit log, revocation clauses, and no-overreach clauses"
        ∷ "explicit statement that downstream W3/B4/origin/W4/W5 blockers are not discharged by the token hook alone"
        ∷ []
    ; noPromotionBoundary =
        "This module is a governance-action request and diagnostic only"
        ∷ "No constructor is added to W3AcceptedEvidenceAuthorityToken here"
        ∷ "No W3AcceptedEvidenceAuthorityToken is constructed here"
        ∷ "No W3AcceptedAuthorityExternalReceipt is constructed here"
        ∷ "No W3EvidenceBackedEmpiricalTarget, B4 empirical promotion, origin promotion, W4/W5 authority, or full empirical promotion is constructed here"
        ∷ []
    }

canonicalW3GovernanceActionRequired :
  W3AcceptedEvidenceAuthorityTokenGovernanceActionRequest.governanceActionRequired
    canonicalW3AcceptedEvidenceAuthorityTokenGovernanceActionRequest
  ≡
  true
canonicalW3GovernanceActionRequired = refl

canonicalW3ExactConstructorOrHookStillAbsent :
  W3AcceptedEvidenceAuthorityTokenGovernanceActionRequest.exactConstructorOrHookPresentNow
    canonicalW3AcceptedEvidenceAuthorityTokenGovernanceActionRequest
  ≡
  false
canonicalW3ExactConstructorOrHookStillAbsent = refl

canonicalW3GovernanceActionRequestConstructsNoAuthorityToken :
  W3AcceptedEvidenceAuthorityTokenGovernanceActionRequest.authorityTokenConstructedHere
    canonicalW3AcceptedEvidenceAuthorityTokenGovernanceActionRequest
  ≡
  false
canonicalW3GovernanceActionRequestConstructsNoAuthorityToken = refl

canonicalW3GovernanceActionRequestLocalChecksumBound :
  W3AcceptedEvidenceAuthorityTokenGovernanceActionRequest.localCanonicalChecksumBound
    canonicalW3AcceptedEvidenceAuthorityTokenGovernanceActionRequest
  ≡
  true
canonicalW3GovernanceActionRequestLocalChecksumBound = refl
