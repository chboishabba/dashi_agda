module DASHI.Core.ConsumerDecisionAdequacyFromReductionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction
import DASHI.Core.ConsumerRelativeApproximateFidelityBridgeExact as Approx

------------------------------------------------------------------------
-- PROOF-DERIVED DECISION ADEQUACY
--
-- `DecisionAdequate model intervention` should not be a free boolean merely
-- because a runtime policy wants one.  This owner derives the substantive
-- witness from either an exact consumer-relative ROM or an approximate
-- discrepancy/margin certificate.
------------------------------------------------------------------------

record ExactDecisionAdequacy
    {Fine Action Summary Intervention : Set}
    (rom : Reduction.ConsumerRelativeReduction Fine Action Summary)
    (decide : Summary → Intervention)
    (intervention : Intervention) : Set₁ where
  constructor exactDecisionAdequacy
  field
    trace : List Action
    Live : Fine → Set
    fineSelectsIntervention :
      (state : Fine) →
      Live state →
      decide
        (Reduction.fineObserve rom
          (Reduction.run (Reduction.fineStep rom) trace state))
      ≡ intervention
    consumerReference : String
    scopeReference : String

open ExactDecisionAdequacy public

exactReducedDecisionSelectsSameIntervention :
  ∀ {Fine Action Summary Intervention}
    {rom : Reduction.ConsumerRelativeReduction Fine Action Summary}
    {decide : Summary → Intervention}
    {intervention : Intervention} →
  (adequacy : ExactDecisionAdequacy rom decide intervention) →
  (state : Fine) →
  Live adequacy state →
  decide
    (Reduction.reducedObserve rom
      (Reduction.run (Reduction.reducedStep rom)
        (trace adequacy)
        (Reduction.encode rom state)))
  ≡ intervention
exactReducedDecisionSelectsSameIntervention {rom = rom} {decide = decide}
    adequacy state liveState =
  trans
    (Approx.exactReductionDecisionSafe
      rom decide ((trace adequacy) , state))
    (fineSelectsIntervention adequacy state liveState)

record ApproximateDecisionAdequacy
    {Fine Action Summary Intervention : Set}
    (model : Approx.ApproximateTraceReduction Fine Action Summary)
    (decide : Summary → Intervention)
    (intervention : Intervention) : Set₁ where
  constructor approximateDecisionAdequacy
  field
    certificate : Approx.ApproximateDecisionCertificate model decide
    trace : List Action
    Live : Fine → Set
    fineSelectsIntervention :
      (state : Fine) →
      Live state →
      decide
        (Approx.fineSummary model
          (Reduction.run (Approx.fineStep model) trace state))
      ≡ intervention
    consumerReference : String
    scopeReference : String

open ApproximateDecisionAdequacy public

approximateReducedDecisionSelectsSameIntervention :
  ∀ {Fine Action Summary Intervention}
    {model : Approx.ApproximateTraceReduction Fine Action Summary}
    {decide : Summary → Intervention}
    {intervention : Intervention} →
  (adequacy : ApproximateDecisionAdequacy model decide intervention) →
  (state : Fine) →
  ApproximateDecisionAdequacy.Live adequacy state →
  decide
    (Approx.reducedSummary model
      (Reduction.run (Approx.reducedStep model)
        (ApproximateDecisionAdequacy.trace adequacy)
        (Approx.encode model state)))
  ≡ intervention
approximateReducedDecisionSelectsSameIntervention adequacy state liveState =
  trans
    (Approx.approximateReductionDecisionSafe
      (certificate adequacy)
      ((ApproximateDecisionAdequacy.trace adequacy) , state))
    (ApproximateDecisionAdequacy.fineSelectsIntervention adequacy state liveState)

------------------------------------------------------------------------
-- Runtime model identifiers are deliberately separate from rich proof objects.
-- Applications declare which exact/approximate proof object a runtime model
-- identifier realizes; adequacy is then generated only by the two certificate
-- constructors below.
------------------------------------------------------------------------

data DerivedDecisionAdequacy
    {ModelState Fine Action Summary Intervention : Set}
    (ExactRealises :
      ModelState →
      Reduction.ConsumerRelativeReduction Fine Action Summary → Set)
    (ApproxRealises :
      ModelState →
      Approx.ApproximateTraceReduction Fine Action Summary → Set) :
    ModelState → Intervention → Set₂ where

  exactAdequate :
    ∀ {runtimeModel intervention}
      (rom : Reduction.ConsumerRelativeReduction Fine Action Summary) →
      ExactRealises runtimeModel rom →
      (decide : Summary → Intervention) →
      ExactDecisionAdequacy rom decide intervention →
    DerivedDecisionAdequacy ExactRealises ApproxRealises
      runtimeModel intervention

  approximateAdequate :
    ∀ {runtimeModel intervention}
      (model : Approx.ApproximateTraceReduction Fine Action Summary) →
      ApproxRealises runtimeModel model →
      (decide : Summary → Intervention) →
      ApproximateDecisionAdequacy model decide intervention →
    DerivedDecisionAdequacy ExactRealises ApproxRealises
      runtimeModel intervention

------------------------------------------------------------------------
-- The joint runtime planner currently consumes a first-order Set-valued
-- adequacy token.  This interface is an exact bridge: every token must decode to
-- a rich proof-derived adequacy witness, and every rich witness can produce a
-- token.  Hence policy-level adequacy cannot be populated independently of the
-- exact/approximate certificate layer.
------------------------------------------------------------------------

record FirstOrderAdequacyInterface
    {ModelState Fine Action Summary Intervention : Set}
    (ExactRealises :
      ModelState →
      Reduction.ConsumerRelativeReduction Fine Action Summary → Set)
    (ApproxRealises :
      ModelState →
      Approx.ApproximateTraceReduction Fine Action Summary → Set) : Set₂ where
  constructor firstOrderAdequacyInterface
  field
    Token : ModelState → Intervention → Set
    proofToToken :
      ∀ {model intervention} →
      DerivedDecisionAdequacy ExactRealises ApproxRealises model intervention →
      Token model intervention
    tokenToProof :
      ∀ {model intervention} →
      Token model intervention →
      DerivedDecisionAdequacy ExactRealises ApproxRealises model intervention
    interfaceReference : String

open FirstOrderAdequacyInterface public

record ConsumerDecisionAdequacyBoundary : Set where
  constructor consumerDecisionAdequacyBoundary
  field
    exactROMCanProduceDecisionAdequacy : Bool
    exactROMCanProduceDecisionAdequacyIsTrue :
      exactROMCanProduceDecisionAdequacy ≡ true

    approximateMarginCertificateCanProduceDecisionAdequacy : Bool
    approximateMarginCertificateCanProduceDecisionAdequacyIsTrue :
      approximateMarginCertificateCanProduceDecisionAdequacy ≡ true

    lowErrorWithoutConsumerMarginIsAdequacy : Bool
    lowErrorWithoutConsumerMarginIsAdequacyIsFalse :
      lowErrorWithoutConsumerMarginIsAdequacy ≡ false

    runtimeModelIdentifierIsSameObjectAsProofBearingROM : Bool
    runtimeModelIdentifierIsSameObjectAsProofBearingROMIsFalse :
      runtimeModelIdentifierIsSameObjectAsProofBearingROM ≡ false

    firstOrderPolicyTokenMayExistWithoutRichAdequacyProof : Bool
    firstOrderPolicyTokenMayExistWithoutRichAdequacyProofIsFalse :
      firstOrderPolicyTokenMayExistWithoutRichAdequacyProof ≡ false

canonicalConsumerDecisionAdequacyBoundary : ConsumerDecisionAdequacyBoundary
canonicalConsumerDecisionAdequacyBoundary =
  consumerDecisionAdequacyBoundary
    true refl true refl false refl false refl false refl
