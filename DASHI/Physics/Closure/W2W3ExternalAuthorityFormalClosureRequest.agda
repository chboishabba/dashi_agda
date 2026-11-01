module DASHI.Physics.Closure.W2W3ExternalAuthorityFormalClosureRequest where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation as W2
import DASHI.Physics.Closure.W2GovernanceTokenConstructorObstruction as W2Obs
import DASHI.Physics.Closure.W2W3GovernancePolicyHookRequest as Hook
import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptRequestPack as W3Pack
import DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate as W3Gate
import DASHI.Physics.Closure.W3AcceptedEvidenceAuthorityTokenGovernanceObstruction as W3Obs

------------------------------------------------------------------------
-- W2/W3 Option B external-authority formal closure request.
--
-- Option B is not an instruction to add constructors and not a missing
-- internal-token proof.  It is the closed current formal status: the policy
-- evidence is consumed, token construction remains explicitly local-false,
-- and progress is pending an external accepted-authority receipt/value of the
-- exact authority-token types.

data W2W3OptionBFormalClosureStatus : Set where
  pendingExternalAuthorityReceipt :
    W2W3OptionBFormalClosureStatus

data W2W3OptionBInternalProofStatus : Set where
  notMissingInternalTokenProof :
    W2W3OptionBInternalProofStatus

data W2W3OptionBLocalConstructionStatus : Set where
  noLocalAuthorityTokenConstruction :
    W2W3OptionBLocalConstructionStatus

data W2W3OptionBExternalReceiptRequirement : Set where
  exactExternalAuthorityReceiptRequired :
    W2W3OptionBExternalReceiptRequirement

record W2W3ExternalAuthorityFormalClosureRequest : Setω where
  field
    governanceHookRequest :
      Hook.W2W3GovernancePolicyHookRequest

    constructorAuthorizationDiagnostic :
      Hook.W2W3PolicyConstructorAuthorizationDiagnostic

    w2ConstructorObstruction :
      W2Obs.W2GovernanceTokenConstructorObstruction

    w3ConstructorObstruction :
      W3Obs.W3AcceptedEvidenceAuthorityTokenGovernanceObstruction

    w3ExternalProviderRequest :
      W3Pack.W3AcceptedAuthorityProviderPayloadRequest

    optionBStatus :
      W2W3OptionBFormalClosureStatus

    internalProofStatus :
      W2W3OptionBInternalProofStatus

    localConstructionStatus :
      W2W3OptionBLocalConstructionStatus

    externalReceiptRequirement :
      W2W3OptionBExternalReceiptRequirement

    policyEvidenceConsumed :
      Bool

    policyEvidenceConsumedIsTrue :
      policyEvidenceConsumed
      ≡
      true

    tokensConstructedByThisPolicy :
      Bool

    tokensConstructedByThisPolicyIsFalse :
      tokensConstructedByThisPolicy
      ≡
      false

    tokenProducingHookAuthorizedNow :
      Bool

    tokenProducingHookAuthorizedNowIsFalse :
      tokenProducingHookAuthorizedNow
      ≡
      false

    w2LocalTokenConstructed :
      Bool

    w2LocalTokenConstructedIsFalse :
      w2LocalTokenConstructed
      ≡
      false

    w3LocalTokenConstructed :
      Bool

    w3LocalTokenConstructedIsFalse :
      w3LocalTokenConstructed
      ≡
      false

    w2AuthorityTokenUnavailable :
      W2.NaturalP2ConvergencePromotionAuthorityToken →
      ⊥

    w3AuthorityTokenUnavailable :
      W3Gate.W3AcceptedEvidenceAuthorityToken →
      ⊥

    w3FirstExternalProviderField :
      W3Pack.W3AcceptedAuthorityProviderMissingField

    w3FirstExternalProviderFieldIsAuthorityToken :
      w3FirstExternalProviderField
      ≡
      W3Pack.missingAcceptedEvidenceAuthorityToken

    notInternalTokenProofGap :
      List String

    pendingExternalReceiptSurface :
      List String

    noLocalConstructionBoundary :
      List String

canonicalW2W3ExternalAuthorityFormalClosureRequest :
  W2W3ExternalAuthorityFormalClosureRequest
canonicalW2W3ExternalAuthorityFormalClosureRequest =
  record
    { governanceHookRequest =
        Hook.canonicalW2W3GovernancePolicyHookRequest
    ; constructorAuthorizationDiagnostic =
        Hook.canonicalW2W3PolicyConstructorAuthorizationDiagnostic
    ; w2ConstructorObstruction =
        W2Obs.canonicalW2GovernanceTokenConstructorObstruction
    ; w3ConstructorObstruction =
        W3Obs.canonicalW3AcceptedEvidenceAuthorityTokenGovernanceObstruction
    ; w3ExternalProviderRequest =
        W3Pack.canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; optionBStatus =
        pendingExternalAuthorityReceipt
    ; internalProofStatus =
        notMissingInternalTokenProof
    ; localConstructionStatus =
        noLocalAuthorityTokenConstruction
    ; externalReceiptRequirement =
        exactExternalAuthorityReceiptRequired
    ; policyEvidenceConsumed =
        Hook.W2W3GovernancePolicyHookRequest.typedPolicyEvidenceConsumed
          Hook.canonicalW2W3GovernancePolicyHookRequest
    ; policyEvidenceConsumedIsTrue =
        refl
    ; tokensConstructedByThisPolicy =
        Hook.DASHIGovernanceSelfIssuancePolicyEvidence.tokensConstructedByThisPolicy
          Hook.canonicalDASHIGovernanceSelfIssuancePolicyEvidence
    ; tokensConstructedByThisPolicyIsFalse =
        refl
    ; tokenProducingHookAuthorizedNow =
        Hook.W2W3GovernancePolicyHookRequest.tokenProducingHookAuthorizedNow
          Hook.canonicalW2W3GovernancePolicyHookRequest
    ; tokenProducingHookAuthorizedNowIsFalse =
        refl
    ; w2LocalTokenConstructed =
        Hook.W2GovernanceHookEvidenceConsumption.authorityTokenConstructedHere
          Hook.canonicalW2GovernanceHookEvidenceConsumption
    ; w2LocalTokenConstructedIsFalse =
        refl
    ; w3LocalTokenConstructed =
        Hook.W3GovernanceHookEvidenceConsumption.authorityTokenConstructedHere
          Hook.canonicalW3GovernanceHookEvidenceConsumption
    ; w3LocalTokenConstructedIsFalse =
        refl
    ; w2AuthorityTokenUnavailable =
        W2.naturalP2ConvergencePromotionAuthorityUnavailable
    ; w3AuthorityTokenUnavailable =
        W3Obs.w3AcceptedEvidenceAuthorityTokenStillUninhabited
    ; w3FirstExternalProviderField =
        W3Pack.missingAcceptedEvidenceAuthorityToken
    ; w3FirstExternalProviderFieldIsAuthorityToken =
        refl
    ; notInternalTokenProofGap =
        "Option B does not ask the repo to prove an internal token inhabitant"
        ∷ "The current hook already records policyEvidenceConsumed=true"
        ∷ "The current hook also records tokenProducingHookAuthorizedNow=false"
        ∷ "W2/W3 remain blocked because exact external authority-token receipts are absent"
        ∷ []
    ; pendingExternalReceiptSurface =
        "W2 awaits an external authority value or accepted receipt for NaturalP2ConvergencePromotionAuthorityToken"
        ∷ "W3 awaits an external accepted evidence authority value or receipt for W3AcceptedEvidenceAuthorityToken"
        ∷ "The W3 provider pack first missing field is missingAcceptedEvidenceAuthorityToken"
        ∷ "Any later closure must consume the exact external receipt; this module consumes none"
        ∷ []
    ; noLocalConstructionBoundary =
        "No constructor is added to NaturalP2ConvergencePromotionAuthorityToken"
        ∷ "No constructor is added to W3AcceptedEvidenceAuthorityToken"
        ∷ "No NaturalP2ConvergencePromotionAuthorityToken is constructed locally"
        ∷ "No W3AcceptedEvidenceAuthorityToken is constructed locally"
        ∷ "No W2 or W3 promotion receipt follows from this Option B request"
        ∷ []
    }

canonicalW2W3OptionBPendingExternalReceipt :
  W2W3ExternalAuthorityFormalClosureRequest.optionBStatus
    canonicalW2W3ExternalAuthorityFormalClosureRequest
  ≡
  pendingExternalAuthorityReceipt
canonicalW2W3OptionBPendingExternalReceipt = refl

canonicalW2W3OptionBNotInternalProofGap :
  W2W3ExternalAuthorityFormalClosureRequest.internalProofStatus
    canonicalW2W3ExternalAuthorityFormalClosureRequest
  ≡
  notMissingInternalTokenProof
canonicalW2W3OptionBNotInternalProofGap = refl

canonicalW2W3OptionBNoLocalConstruction :
  W2W3ExternalAuthorityFormalClosureRequest.localConstructionStatus
    canonicalW2W3ExternalAuthorityFormalClosureRequest
  ≡
  noLocalAuthorityTokenConstruction
canonicalW2W3OptionBNoLocalConstruction = refl

canonicalW2W3OptionBTokensConstructedByPolicyFalse :
  W2W3ExternalAuthorityFormalClosureRequest.tokensConstructedByThisPolicy
    canonicalW2W3ExternalAuthorityFormalClosureRequest
  ≡
  false
canonicalW2W3OptionBTokensConstructedByPolicyFalse = refl

canonicalW2W3OptionBHookDoesNotAuthorizeProduction :
  W2W3ExternalAuthorityFormalClosureRequest.tokenProducingHookAuthorizedNow
    canonicalW2W3ExternalAuthorityFormalClosureRequest
  ≡
  false
canonicalW2W3OptionBHookDoesNotAuthorizeProduction = refl

canonicalW2W3OptionBW2NoLocalToken :
  W2W3ExternalAuthorityFormalClosureRequest.w2LocalTokenConstructed
    canonicalW2W3ExternalAuthorityFormalClosureRequest
  ≡
  false
canonicalW2W3OptionBW2NoLocalToken = refl

canonicalW2W3OptionBW3NoLocalToken :
  W2W3ExternalAuthorityFormalClosureRequest.w3LocalTokenConstructed
    canonicalW2W3ExternalAuthorityFormalClosureRequest
  ≡
  false
canonicalW2W3OptionBW3NoLocalToken = refl

canonicalW2W3OptionBFirstW3ExternalFieldIsAuthority :
  W2W3ExternalAuthorityFormalClosureRequest.w3FirstExternalProviderField
    canonicalW2W3ExternalAuthorityFormalClosureRequest
  ≡
  W3Pack.missingAcceptedEvidenceAuthorityToken
canonicalW2W3OptionBFirstW3ExternalFieldIsAuthority = refl
