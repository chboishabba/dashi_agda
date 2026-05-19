module DASHI.Physics.Closure.W2GovernanceTokenConstructorObstruction where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Set; Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation as W2
import DASHI.Physics.Closure.W2GovernanceSelfIssuanceIntakeRequest as Intake
import DASHI.Physics.Closure.W2PromotionAuthorityReceipt as Audit

------------------------------------------------------------------------
-- W2 governance-token constructor obstruction.
--
-- The landed governance policy permits bounded self-issuance classes, but it
-- also states that the policy constructs no token by itself.  This module is
-- the W2 typed receipt for that distinction: class-level permission is not an
-- inhabitant of the constructorless authority-token datatype.

data W2GovernancePolicyEvidenceClass : Set where
  reflProvedInternalEvidence :
    W2GovernancePolicyEvidenceClass

data W2GovernanceTokenConstructionStatus : Set where
  policyPermitsClassButTokenConstructorAbsent :
    W2GovernanceTokenConstructionStatus

data W2FirstMissingAuthorityConstructor : Set where
  missingNaturalP2ConvergencePromotionAuthorityConstructor :
    W2FirstMissingAuthorityConstructor

data W2FirstMissingTypedInterface : Set where
  missingNaturalP2PromotionAuthorityConstructorOrPolicyHook :
    W2FirstMissingTypedInterface

record W2GovernanceTokenConstructorObstruction : Setω where
  field
    policyDocument :
      String

    evidenceClass :
      W2GovernancePolicyEvidenceClass

    policyPermitsEvidenceClass :
      Bool

    policyPermitsEvidenceClassIsTrue :
      policyPermitsEvidenceClass ≡ true

    tokensConstructedByPolicy :
      Bool

    tokensConstructedByPolicyIsFalse :
      tokensConstructedByPolicy ≡ false

    constructionStatus :
      W2GovernanceTokenConstructionStatus

    firstMissingConstructor :
      W2FirstMissingAuthorityConstructor

    firstMissingTypedInterface :
      W2FirstMissingTypedInterface

    exactTokenDefinitionModule :
      String

    exactTokenDefinitionForm :
      String

    firstMissingPromotionField :
      W2.NaturalP2ConvergenceMissingField

    authorityTokenUnavailable :
      W2.NaturalP2ConvergencePromotionAuthorityToken → ⊥

    promotionReceiptImpossible :
      W2.NaturalP2ConvergencePromotionReceipt → ⊥

    w2Audit :
      Audit.W2PromotionAuthorityAuditDiagnostic

    w2GovernanceIntake :
      Intake.W2GovernanceSelfIssuanceIntakeRequest

    remainingPayloadFieldsAfterAuthority :
      List W2.NaturalP2ConvergenceMissingField

    exactPolicyHookInterfaceRequired :
      List String

    constructorRequest :
      List String

    noPromotionBoundary :
      List String

canonicalW2GovernanceTokenConstructorObstruction :
  W2GovernanceTokenConstructorObstruction
canonicalW2GovernanceTokenConstructorObstruction =
  record
    { policyDocument =
        "Docs/DASHIGovernanceSelfIssuancePolicy.md"
    ; evidenceClass =
        reflProvedInternalEvidence
    ; policyPermitsEvidenceClass =
        true
    ; policyPermitsEvidenceClassIsTrue =
        refl
    ; tokensConstructedByPolicy =
        false
    ; tokensConstructedByPolicyIsFalse =
        refl
    ; constructionStatus =
        policyPermitsClassButTokenConstructorAbsent
    ; firstMissingConstructor =
        missingNaturalP2ConvergencePromotionAuthorityConstructor
    ; firstMissingTypedInterface =
        missingNaturalP2PromotionAuthorityConstructorOrPolicyHook
    ; exactTokenDefinitionModule =
        "DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation"
    ; exactTokenDefinitionForm =
        "data NaturalP2ConvergencePromotionAuthorityToken : Set where"
    ; firstMissingPromotionField =
        W2.missingPromotionAuthorityToken
    ; authorityTokenUnavailable =
        W2.naturalP2ConvergencePromotionAuthorityUnavailable
    ; promotionReceiptImpossible =
        W2.naturalP2ConvergencePromotionReceiptImpossible
    ; w2Audit =
        Audit.canonicalW2PromotionAuthorityAuditDiagnostic
    ; w2GovernanceIntake =
        Intake.canonicalW2GovernanceSelfIssuanceIntakeRequest
    ; remainingPayloadFieldsAfterAuthority =
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
    ; exactPolicyHookInterfaceRequired =
        "A constructor in NaturalP2ConvergencePromotionAuthorityToken, or an imported non-postulated typed hook whose result type is exactly NaturalP2ConvergencePromotionAuthorityToken"
        ∷ "The hook must consume Docs/DASHIGovernanceSelfIssuancePolicy.md as policy evidence, not as an untyped prose assumption"
        ∷ "The hook must name tokenName = NaturalP2ConvergencePromotionAuthorityToken and laneScope = W2 natural-p2-convergence"
        ∷ "The hook must carry the exact W2 evidence packet, audit conditions, revocation conditions, and no-overreach clauses required by the policy"
        ∷ "Until that interface exists, NaturalP2ConvergencePromotionReceipt.promotionAuthority is the first uninhabited receipt field"
        ∷ []
    ; constructorRequest =
        "First missing constructor: NaturalP2ConvergencePromotionAuthorityToken constructor"
        ∷ "Acceptable alternative: a typed governance-policy hook that inhabits NaturalP2ConvergencePromotionAuthorityToken without postulates"
        ∷ "The constructor or hook must name the exact bounded W2 evidence packet, audit conditions, revocation conditions, and no-overreach clauses"
        ∷ []
    ; noPromotionBoundary =
        "The governance policy permits the refl-proved-internal evidence class, but tokensConstructedByPolicy is false"
        ∷ "No NaturalP2ConvergencePromotionAuthorityToken is constructed here"
        ∷ "No NaturalP2ConvergencePromotionReceipt is constructed here"
        ∷ "Natural p2 bridge/coherence and carrier-general convergence payload fields remain separate missing receipts after authority"
        ∷ []
    }

canonicalW2PolicyPermitsClass :
  W2GovernanceTokenConstructorObstruction.policyPermitsEvidenceClass
    canonicalW2GovernanceTokenConstructorObstruction
    ≡
  true
canonicalW2PolicyPermitsClass = refl

canonicalW2PolicyConstructsNoToken :
  W2GovernanceTokenConstructorObstruction.tokensConstructedByPolicy
    canonicalW2GovernanceTokenConstructorObstruction
    ≡
  false
canonicalW2PolicyConstructsNoToken = refl
