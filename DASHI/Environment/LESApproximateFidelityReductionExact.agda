module DASHI.Environment.LESApproximateFidelityReductionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerRelativeApproximateFidelityBridgeExact as Approximate
import DASHI.Core.AdaptiveFidelityConsumerMarginExact as Fidelity
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis

------------------------------------------------------------------------
-- LES adapter for practical approximate ROMs.
--
-- Exact ConsumerRelativeReduction remains the strongest route.  This adapter is
-- for surrogates which do not exactly commute at state level but possess a
-- calibrated trace discrepancy that lies inside a declared consumer decision
-- margin.  It therefore reuses the repo's adaptive-fidelity theorem directly.
------------------------------------------------------------------------

record LESApproximateReduction
    (mechanism : Basis.DomainMechanismSocket)
    (Summary : Set) : Set₁ where
  constructor lesApproximateReduction
  field
    Reduced : Set
    encode : Basis.State mechanism → Reduced
    reducedStep : Basis.Control mechanism → Reduced → Reduced
    fineSummary : Basis.State mechanism → Summary
    reducedSummary : Reduced → Summary
    lowModelReference : String
    highModelReference : String
    approximationScopeReference : String

open LESApproximateReduction public

asApproximateTraceReduction :
  ∀ {mechanism Summary} →
  LESApproximateReduction mechanism Summary →
  Approximate.ApproximateTraceReduction
    (Basis.State mechanism)
    (Basis.Control mechanism)
    Summary
asApproximateTraceReduction {mechanism} model =
  Approximate.approximateTraceReduction
    (Reduced model)
    (encode model)
    (Basis.evolve mechanism)
    (reducedStep model)
    (fineSummary model)
    (reducedSummary model)
    (lowModelReference model)
    (highModelReference model)
    (approximationScopeReference model)

record LESApproximateDecisionCertificate
    {mechanism : Basis.DomainMechanismSocket}
    {Summary Decision : Set}
    (model : LESApproximateReduction mechanism Summary)
    (decide : Summary → Decision) : Set₁ where
  constructor lesApproximateDecisionCertificate
  field
    certificate :
      Approximate.ApproximateDecisionCertificate
        (asApproximateTraceReduction model)
        decide
    applicationReference : String
    calibrationRegionReference : String
    heldOutRegionReference : String
    consumerReference : String

open LESApproximateDecisionCertificate public

lesApproximateDecisionSafe :
  ∀ {mechanism Summary Decision}
    {model : LESApproximateReduction mechanism Summary}
    {decide : Summary → Decision} →
  LESApproximateDecisionCertificate model decide →
  (controls : List (Basis.Control mechanism)) →
  (state : Basis.State mechanism) →
  decide
    (Fidelity.low
      (Approximate.approximateTraceFidelityPair
        (asApproximateTraceReduction model))
      (controls , state))
  ≡ decide
    (Fidelity.high
      (Approximate.approximateTraceFidelityPair
        (asApproximateTraceReduction model))
      (controls , state))
lesApproximateDecisionSafe receipt controls state =
  Approximate.approximateReductionDecisionSafe
    (certificate receipt)
    (controls , state)

------------------------------------------------------------------------
-- Exact future-safety failure and decision-margin safety are deliberately not
-- identified.  A state/summary mismatch may be irrelevant to a coarser declared
-- decision; conversely decision safety does not certify a richer consumer.
------------------------------------------------------------------------

record LESApproximateReductionBoundary : Set where
  constructor lesApproximateReductionBoundary
  field
    exactStateCommutationRequiredForDecisionMarginRoute : Bool
    exactStateCommutationRequiredForDecisionMarginRouteIsFalse :
      exactStateCommutationRequiredForDecisionMarginRoute ≡ false
    certifiedTraceDiscrepancyAndMarginCanSufficeForDecision : Bool
    certifiedTraceDiscrepancyAndMarginCanSufficeForDecisionIsTrue :
      certifiedTraceDiscrepancyAndMarginCanSufficeForDecision ≡ true
    decisionSafeApproximationIsExactFutureQuotient : Bool
    decisionSafeApproximationIsExactFutureQuotientIsFalse :
      decisionSafeApproximationIsExactFutureQuotient ≡ false
    decisionSafeApproximationIsMechanisticRealization : Bool
    decisionSafeApproximationIsMechanisticRealizationIsFalse :
      decisionSafeApproximationIsMechanisticRealization ≡ false

canonicalLESApproximateReductionBoundary : LESApproximateReductionBoundary
canonicalLESApproximateReductionBoundary =
  lesApproximateReductionBoundary false refl true refl false refl false refl
