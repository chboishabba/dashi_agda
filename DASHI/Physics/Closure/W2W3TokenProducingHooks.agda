module DASHI.Physics.Closure.W2W3TokenProducingHooks where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Set; Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Arithmetic.UniformConvergenceRateSurface as W2Rate
import DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation as W2
import DASHI.Physics.Closure.W2GovernanceSelfIssuanceIntakeRequest as W2Intake
import DASHI.Physics.Closure.W2GovernanceTokenConstructorObstruction as W2Obs
import DASHI.Physics.Closure.W2W3GovernancePolicyHookRequest as Hook
import DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate as W3Gate
import DASHI.Physics.Closure.W3AcceptedEvidenceAuthorityTokenGovernanceObstruction as W3Obs
import DASHI.Physics.Closure.W3AcceptedEvidenceAuthorityTokenIntakeRequest as W3Intake
import DASHI.Physics.Closure.W3CanonicalChecksumBindingReceipt as W3Checksum

------------------------------------------------------------------------
-- W2/W3 token-producing hook request surface.
--
-- The exact W2 and W3 authority-token datatypes are currently empty.  This
-- module therefore records the requested hook result types and payload fields
-- without constructing either token or pretending that the policy hook exists.

data W2W3TokenProducingHookState : Set where
  exactHookRequestedButTokenDatatypeConstructorless :
    W2W3TokenProducingHookState

data W2W3TokenConstructionMark : Set where
  tokenUnconstructedBecauseExactDatatypeHasNoConstructor :
    W2W3TokenConstructionMark

record W2TokenProducingHookRequest : Setω where
  field
    hookState :
      W2W3TokenProducingHookState

    tokenConstructionMark :
      W2W3TokenConstructionMark

    policyEvidence :
      Hook.DASHIGovernanceSelfIssuancePolicyEvidence

    governanceIntake :
      W2Intake.W2GovernanceSelfIssuanceIntakeRequest

    constructorObstruction :
      W2Obs.W2GovernanceTokenConstructorObstruction

    uniformRateEvidence :
      W2Rate.UniformNormalizeAddRateDiagnostic

    requestedResultType :
      Set

    requestedResultTypeIsExact :
      requestedResultType
      ≡
      W2.NaturalP2ConvergencePromotionAuthorityToken

    exactTokenName :
      String

    laneScope :
      String

    hookWouldProduceToken :
      Bool

    hookWouldProduceTokenIsFalse :
      hookWouldProduceToken
      ≡
      false

    tokenConstructedHere :
      Bool

    tokenConstructedHereIsFalse :
      tokenConstructedHere
      ≡
      false

    tokenUnavailable :
      W2.NaturalP2ConvergencePromotionAuthorityToken →
      ⊥

    nonAuthorityPayloadFields :
      List W2.NaturalP2ConvergenceMissingField

    exactRequiredHookFields :
      List String

    noPromotionBoundary :
      List String

record W3TokenProducingHookRequest : Setω where
  field
    hookState :
      W2W3TokenProducingHookState

    tokenConstructionMark :
      W2W3TokenConstructionMark

    policyEvidence :
      Hook.DASHIGovernanceSelfIssuancePolicyEvidence

    intakeRequest :
      W3Intake.W3AcceptedEvidenceAuthorityTokenIntakeRequest

    constructorObstruction :
      W3Obs.W3AcceptedEvidenceAuthorityTokenGovernanceObstruction

    checksumBindingReceipt :
      W3Checksum.W3CanonicalChecksumBindingReceipt

    requestedResultType :
      Set

    requestedResultTypeIsExact :
      requestedResultType
      ≡
      W3Gate.W3AcceptedEvidenceAuthorityToken

    exactTokenName :
      String

    laneScope :
      String

    hookWouldProduceToken :
      Bool

    hookWouldProduceTokenIsFalse :
      hookWouldProduceToken
      ≡
      false

    tokenConstructedHere :
      Bool

    tokenConstructedHereIsFalse :
      tokenConstructedHere
      ≡
      false

    tokenUnavailable :
      W3Gate.W3AcceptedEvidenceAuthorityToken →
      ⊥

    exactRequiredHookFields :
      List String

    noPromotionBoundary :
      List String

record W2W3TokenProducingHookRequestSurface : Setω where
  field
    w2Request :
      W2TokenProducingHookRequest

    w3Request :
      W3TokenProducingHookRequest

    optionAInternalClaim :
      Bool

    optionAInternalClaimIsTrue :
      optionAInternalClaim
      ≡
      true

    optionAExternalClaim :
      Bool

    optionAExternalClaimIsFalse :
      optionAExternalClaim
      ≡
      false

    constructsAuthorityTokens :
      Bool

    constructsAuthorityTokensIsFalse :
      constructsAuthorityTokens
      ≡
      false

    exactRemainingBlocker :
      List String

canonicalW2TokenProducingHookRequest :
  W2TokenProducingHookRequest
canonicalW2TokenProducingHookRequest =
  record
    { hookState =
        exactHookRequestedButTokenDatatypeConstructorless
    ; tokenConstructionMark =
        tokenUnconstructedBecauseExactDatatypeHasNoConstructor
    ; policyEvidence =
        Hook.canonicalDASHIGovernanceSelfIssuancePolicyEvidence
    ; governanceIntake =
        W2Intake.canonicalW2GovernanceSelfIssuanceIntakeRequest
    ; constructorObstruction =
        W2Obs.canonicalW2GovernanceTokenConstructorObstruction
    ; uniformRateEvidence =
        W2Rate.canonicalUniformNormalizeAddRateDiagnostic
    ; requestedResultType =
        W2.NaturalP2ConvergencePromotionAuthorityToken
    ; requestedResultTypeIsExact =
        refl
    ; exactTokenName =
        "DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation.NaturalP2ConvergencePromotionAuthorityToken"
    ; laneScope =
        "W2 natural-p2-convergence bounded internal self-issuance"
    ; hookWouldProduceToken =
        false
    ; hookWouldProduceTokenIsFalse =
        refl
    ; tokenConstructedHere =
        false
    ; tokenConstructedHereIsFalse =
        refl
    ; tokenUnavailable =
        W2.naturalP2ConvergencePromotionAuthorityUnavailable
    ; nonAuthorityPayloadFields =
        W2Obs.W2GovernanceTokenConstructorObstruction.remainingPayloadFieldsAfterAuthority
          W2Obs.canonicalW2GovernanceTokenConstructorObstruction
    ; exactRequiredHookFields =
        "policyEvidence : DASHIGovernanceSelfIssuancePolicyEvidence"
        ∷ "evidenceClass : reflProvedInternalEvidence"
        ∷ "tokenName : NaturalP2ConvergencePromotionAuthorityToken"
        ∷ "laneScope : W2 natural-p2-convergence"
        ∷ "evidencePacket : normalizeAdd sum/p-adic invariance plus local uniform-rate support"
        ∷ "payloadPackage : natural bridge/coherence and carrier-general convergence receipts"
        ∷ "auditLog : W2PromotionAuthorityAuditDiagnostic"
        ∷ "revocationConditions : policy revocation clauses"
        ∷ "noOverreachClauses : bounded W2 only"
        ∷ []
    ; noPromotionBoundary =
        "This is a hook request surface, not a NaturalP2ConvergencePromotionAuthorityToken"
        ∷ "No W2 authority token is constructed"
        ∷ "No NaturalP2ConvergencePromotionReceipt is constructed"
        ∷ []
    }

canonicalW3TokenProducingHookRequest :
  W3TokenProducingHookRequest
canonicalW3TokenProducingHookRequest =
  record
    { hookState =
        exactHookRequestedButTokenDatatypeConstructorless
    ; tokenConstructionMark =
        tokenUnconstructedBecauseExactDatatypeHasNoConstructor
    ; policyEvidence =
        Hook.canonicalDASHIGovernanceSelfIssuancePolicyEvidence
    ; intakeRequest =
        W3Intake.canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
    ; constructorObstruction =
        W3Obs.canonicalW3AcceptedEvidenceAuthorityTokenGovernanceObstruction
    ; checksumBindingReceipt =
        W3Checksum.canonicalW3CanonicalChecksumBindingReceipt
    ; requestedResultType =
        W3Gate.W3AcceptedEvidenceAuthorityToken
    ; requestedResultTypeIsExact =
        refl
    ; exactTokenName =
        "DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3AcceptedEvidenceAuthorityToken"
    ; laneScope =
        "W3 accepted evidence authority bounded internal/public-evidence self-issuance"
    ; hookWouldProduceToken =
        false
    ; hookWouldProduceTokenIsFalse =
        refl
    ; tokenConstructedHere =
        false
    ; tokenConstructedHereIsFalse =
        refl
    ; tokenUnavailable =
        W3Obs.w3AcceptedEvidenceAuthorityTokenStillUninhabited
    ; exactRequiredHookFields =
        "policyEvidence : DASHIGovernanceSelfIssuancePolicyEvidence"
        ∷ "evidenceClass : publicDOIFrozenCommitEvidence"
        ∷ "tokenName : W3AcceptedEvidenceAuthorityToken"
        ∷ "laneScope : W3 accepted-evidence authority"
        ∷ "evidencePacket : public DOI, frozen commit, t43/t44 canonical payload checksums"
        ∷ "comparisonOrProofLaw : candidate comparison and semantic table matching"
        ∷ "nonCollapseOrNoOverreachWitness : HEPDataW3T43RunnerPerBinNonCollapseReceipt"
        ∷ "auditLog : W3 authority-token intake and governance obstruction"
        ∷ "revocationConditions : policy revocation clauses"
        ∷ "noOverreachClauses : bounded W3 only"
        ∷ []
    ; noPromotionBoundary =
        "This is a hook request surface, not a W3AcceptedEvidenceAuthorityToken"
        ∷ "No W3 authority token is constructed"
        ∷ "No W3AcceptedAuthorityExternalReceipt is constructed"
        ∷ []
    }

canonicalW2W3TokenProducingHookRequestSurface :
  W2W3TokenProducingHookRequestSurface
canonicalW2W3TokenProducingHookRequestSurface =
  record
    { w2Request =
        canonicalW2TokenProducingHookRequest
    ; w3Request =
        canonicalW3TokenProducingHookRequest
    ; optionAInternalClaim =
        true
    ; optionAInternalClaimIsTrue =
        refl
    ; optionAExternalClaim =
        false
    ; optionAExternalClaimIsFalse =
        refl
    ; constructsAuthorityTokens =
        false
    ; constructsAuthorityTokensIsFalse =
        refl
    ; exactRemainingBlocker =
        "NaturalP2ConvergencePromotionAuthorityToken is constructorless; this module records the exact W2 hook request only"
        ∷ "W3AcceptedEvidenceAuthorityToken is constructorless; this module records the exact W3 hook request only"
        ∷ "W2 non-authority payload packaging remains listed in W2TokenProducingHookRequest.nonAuthorityPayloadFields"
        ∷ []
    }

canonicalW2TokenStillUnconstructed :
  W2TokenProducingHookRequest.tokenConstructedHere
    canonicalW2TokenProducingHookRequest
  ≡
  false
canonicalW2TokenStillUnconstructed = refl

canonicalW3TokenStillUnconstructed :
  W3TokenProducingHookRequest.tokenConstructedHere
    canonicalW3TokenProducingHookRequest
  ≡
  false
canonicalW3TokenStillUnconstructed = refl

canonicalW2W3HookSurfaceConstructsNoAuthorityTokens :
  W2W3TokenProducingHookRequestSurface.constructsAuthorityTokens
    canonicalW2W3TokenProducingHookRequestSurface
  ≡
  false
canonicalW2W3HookSurfaceConstructsNoAuthorityTokens = refl
