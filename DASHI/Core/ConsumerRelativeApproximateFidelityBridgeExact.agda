module DASHI.Core.ConsumerRelativeApproximateFidelityBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction
import DASHI.Core.AdaptiveFidelityConsumerMarginExact as Fidelity

------------------------------------------------------------------------
-- PURPOSE
--
-- Exact commuting ROMs are deliberately strong.  Practical surrogates often
-- only need to preserve a declared decision inside a certified discrepancy
-- margin.  This owner reuses AdaptiveFidelityConsumerMarginExact rather than
-- weakening the exact reduction theorem or inventing a second error calculus.
--
-- Exact ROMs embed as the zero-discrepancy/equality special case.
------------------------------------------------------------------------

TraceInput : Set → Set → Set
TraceInput Fine Action = List Action × Fine

------------------------------------------------------------------------
-- Exact reduction -> fidelity pair over arbitrary finite action traces.
------------------------------------------------------------------------

exactTraceFidelityPair :
  ∀ {Fine Action Observation} →
  Reduction.ConsumerRelativeReduction Fine Action Observation →
  Fidelity.FidelityPair (TraceInput Fine Action) Observation
exactTraceFidelityPair rom =
  Fidelity.fidelityPair
    (λ input →
      Reduction.reducedObserve rom
        (Reduction.run (Reduction.reducedStep rom)
          (proj₁ input)
          (Reduction.encode rom (proj₂ input))))
    (λ input →
      Reduction.fineObserve rom
        (Reduction.run (Reduction.fineStep rom)
          (proj₁ input)
          (proj₂ input)))
    "consumer-relative reduced trace"
    "fine trace"

exactTraceEqualityDiscrepancy :
  ∀ {Fine Action Observation}
    (rom : Reduction.ConsumerRelativeReduction Fine Action Observation) →
  Fidelity.BoundedDiscrepancy (exactTraceFidelityPair rom)
exactTraceEqualityDiscrepancy rom =
  Fidelity.boundedDiscrepancy
    _≡_
    "exact commuting consumer-relative reduction"
    []
    bounded
  where
    bounded :
      ∀ input →
      Fidelity.low (exactTraceFidelityPair rom) input
      ≡ Fidelity.high (exactTraceFidelityPair rom) input
    bounded input =
      sym (Reduction.consumerFuturePreserved rom (proj₁ input) (proj₂ input))

equalityDecisionMargin :
  ∀ {Summary Decision : Set} →
  (decide : Summary → Decision) →
  Fidelity.ConsumerDecisionMargin decide
equalityDecisionMargin decide =
  Fidelity.consumerDecisionMargin
    _≡_
    (λ same → cong decide same)
    "definitional/equality decision margin"

exactTraceBoundImpliesEqualityMargin :
  ∀ {Fine Action Observation Decision}
    {rom : Reduction.ConsumerRelativeReduction Fine Action Observation}
    {decide : Observation → Decision} →
  Fidelity.FidelityInsideConsumerMargin
    (exactTraceEqualityDiscrepancy rom)
    (equalityDecisionMargin decide)
exactTraceBoundImpliesEqualityMargin =
  Fidelity.fidelityInsideConsumerMargin (λ same → same)

exactReductionDecisionSafe :
  ∀ {Fine Action Observation Decision}
    (rom : Reduction.ConsumerRelativeReduction Fine Action Observation) →
  (decide : Observation → Decision) →
  (input : TraceInput Fine Action) →
  decide (Fidelity.low (exactTraceFidelityPair rom) input)
  ≡ decide (Fidelity.high (exactTraceFidelityPair rom) input)
exactReductionDecisionSafe rom decide input =
  Fidelity.lowFidelityDecisionIsSafe
    (exactTraceEqualityDiscrepancy rom)
    (equalityDecisionMargin decide)
    exactTraceBoundImpliesEqualityMargin
    input

------------------------------------------------------------------------
-- Approximate reduction surface.  No exact commuting square is asserted.
-- Instead, the entire finite trace is compared through the existing fidelity
-- discrepancy/margin theorem.
------------------------------------------------------------------------

record ApproximateTraceReduction
    (Fine Action Summary : Set) : Set₁ where
  constructor approximateTraceReduction
  field
    Reduced : Set
    encode : Fine → Reduced
    fineStep : Action → Fine → Fine
    reducedStep : Action → Reduced → Reduced
    fineSummary : Fine → Summary
    reducedSummary : Reduced → Summary
    lowModelReference : String
    highModelReference : String
    approximationScopeReference : String

open ApproximateTraceReduction public

approximateTraceFidelityPair :
  ∀ {Fine Action Summary} →
  ApproximateTraceReduction Fine Action Summary →
  Fidelity.FidelityPair (TraceInput Fine Action) Summary
approximateTraceFidelityPair model =
  Fidelity.fidelityPair
    (λ input →
      reducedSummary model
        (Reduction.run (reducedStep model)
          (proj₁ input)
          (encode model (proj₂ input))))
    (λ input →
      fineSummary model
        (Reduction.run (fineStep model)
          (proj₁ input)
          (proj₂ input)))
    (lowModelReference model)
    (highModelReference model)

record ApproximateDecisionCertificate
    {Fine Action Summary Decision : Set}
    (model : ApproximateTraceReduction Fine Action Summary)
    (decide : Summary → Decision) : Set₁ where
  constructor approximateDecisionCertificate
  field
    discrepancy : Fidelity.BoundedDiscrepancy (approximateTraceFidelityPair model)
    margin : Fidelity.ConsumerDecisionMargin decide
    boundInsideMargin : Fidelity.FidelityInsideConsumerMargin discrepancy margin
    calibrationReference : String
    heldOutDiscrepancyReference : String
    consumerScopeReference : String

open ApproximateDecisionCertificate public

approximateReductionDecisionSafe :
  ∀ {Fine Action Summary Decision}
    {model : ApproximateTraceReduction Fine Action Summary}
    {decide : Summary → Decision} →
  ApproximateDecisionCertificate model decide →
  (input : TraceInput Fine Action) →
  decide (Fidelity.low (approximateTraceFidelityPair model) input)
  ≡ decide (Fidelity.high (approximateTraceFidelityPair model) input)
approximateReductionDecisionSafe certificate =
  Fidelity.lowFidelityDecisionIsSafe
    (discrepancy certificate)
    (margin certificate)
    (boundInsideMargin certificate)

record ConsumerApproximateFidelityBoundary : Set where
  constructor consumerApproximateFidelityBoundary
  field
    exactROMIsEqualityDiscrepancySpecialCase : Bool
    exactROMIsEqualityDiscrepancySpecialCaseIsTrue :
      exactROMIsEqualityDiscrepancySpecialCase ≡ true
    approximateROMNeedsExactStateCommutation : Bool
    approximateROMNeedsExactStateCommutationIsFalse :
      approximateROMNeedsExactStateCommutation ≡ false
    approximateROMNeedsCertifiedConsumerMargin : Bool
    approximateROMNeedsCertifiedConsumerMarginIsTrue :
      approximateROMNeedsCertifiedConsumerMargin ≡ true
    lowGlobalErrorAloneIsDecisionSafety : Bool
    lowGlobalErrorAloneIsDecisionSafetyIsFalse :
      lowGlobalErrorAloneIsDecisionSafety ≡ false
    approximateDecisionSafetyImpliesMechanisticRealization : Bool
    approximateDecisionSafetyImpliesMechanisticRealizationIsFalse :
      approximateDecisionSafetyImpliesMechanisticRealization ≡ false

canonicalConsumerApproximateFidelityBoundary :
  ConsumerApproximateFidelityBoundary
canonicalConsumerApproximateFidelityBoundary =
  consumerApproximateFidelityBoundary true refl false refl true refl false refl false refl
