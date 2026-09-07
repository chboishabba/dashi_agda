module DASHI.Analysis.RiemannG2ClayTerminalOneLeafCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannPlattTrudgianCanonicalLowRegionExact as Low
import DASHI.Analysis.RiemannG2UniformIndependentComplementHighProducerExact as High
import DASHI.Analysis.RiemannCriticalLineStabilityRefinementExact as Stability
import DASHI.Analysis.RiemannG2ConstructiveNegativeRHCompletionExact as Negative

------------------------------------------------------------------------
-- CLAY-FACING TERMINAL CUT
--
-- All assembly below is exact and the canonical route is allowance-free.
-- The full same-substrate RH theorem needs:
--
--   L. one exact Platt--Trudgian verified-region transport on this analytic
--      completed-zeta carrier;
--   H. for every chosen High zero assumed off-line, one direct independent
--      literal complement-margin case;
--   C. a cover saying every nontrivial zero is in the verified region or High;
--   S. an exact refinement of the abstract completed-zeta criticalLine
--      predicate to a concrete stable predicate.
--
-- There is no arbitrary Low predicate on the canonical path: Low is
-- definitionally the verified region supplied by L.  L+H+C compile first to
-- constructive double-negated RH.  S is used only in the final logical
-- conversion to positive prize-facing RH.
------------------------------------------------------------------------

record ClayTerminalOneLeafInput
    (analytic : Analytic.AnalyticSubstrate) : Set₁ where
  field
    lowTransport :
      Low.PlattTrudgianVerifiedRegionTransport analytic

    HighRegion : Universal.AnalyticNontrivialZero analytic -> Set

    verifiedOrHighCover :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      Low.CanonicalLowRegion lowTransport rho ⊎ HighRegion rho

    highProducer :
      High.UniformIndependentComplementHighProducer analytic HighRegion

    criticalLineRefinement :
      Stability.CriticalLinePredicateRefinement analytic

    terminalReference : String

open ClayTerminalOneLeafInput public

compiledNegativeRHInput :
  forall {analytic} ->
  ClayTerminalOneLeafInput analytic ->
  Negative.DirectOneLeafNegativeRHInput analytic
compiledNegativeRHInput input = record
  { Negative.lowTransport = lowTransport input
  ; Negative.HighRegion = HighRegion input
  ; Negative.verifiedOrHighCover = verifiedOrHighCover input
  ; Negative.highProducer = highProducer input
  ; Negative.completionReference = terminalReference input
  }

compiledDoubleNegatedRH :
  forall {analytic} ->
  ClayTerminalOneLeafInput analytic ->
  Negative.DoubleNegatedRiemannHypothesisFor analytic
compiledDoubleNegatedRH input =
  Negative.compileDirectOneLeafNegativeRH (compiledNegativeRHInput input)

compiledCriticalLineStable :
  forall {analytic} ->
  ClayTerminalOneLeafInput analytic ->
  Universal.CriticalLineStable analytic
compiledCriticalLineStable input =
  Stability.compileCriticalLineStable (criticalLineRefinement input)

compileClayTerminalOneLeafToRH :
  forall {analytic} ->
  ClayTerminalOneLeafInput analytic ->
  Analytic.RiemannHypothesisFor analytic
compileClayTerminalOneLeafToRH input =
  Negative.negativeRHPlusPredicateRefinementImpliesRH
    (criticalLineRefinement input)
    (compiledDoubleNegatedRH input)

------------------------------------------------------------------------
-- BOUNDARY
------------------------------------------------------------------------

record ClayTerminalOneLeafBoundary : Set where
  constructor clay-terminal-one-leaf-boundary
  field
    consumerAssignedAllowanceLayerOnCanonicalPath : Bool
    consumerAssignedAllowanceLayerOnCanonicalPathIsFalse :
      consumerAssignedAllowanceLayerOnCanonicalPath ≡ false

    extraHighOrdinatePaymentAfterUniformOneLeafProducer : Bool
    extraHighOrdinatePaymentAfterUniformOneLeafProducerIsFalse :
      extraHighOrdinatePaymentAfterUniformOneLeafProducer ≡ false

    separateNearEnvelopePrimitiveLeaf : Bool
    separateNearEnvelopePrimitiveLeafIsFalse :
      separateNearEnvelopePrimitiveLeaf ≡ false

    separateGammaEnvelopePrimitiveLeaf : Bool
    separateGammaEnvelopePrimitiveLeafIsFalse :
      separateGammaEnvelopePrimitiveLeaf ≡ false

    uniformIndependentComplementMarginIsHighAnalyticFamily : Bool
    uniformIndependentComplementMarginIsHighAnalyticFamilyIsTrue :
      uniformIndependentComplementMarginIsHighAnalyticFamily ≡ true

    arbitraryLowPredicateOnCanonicalPath : Bool
    arbitraryLowPredicateOnCanonicalPathIsFalse :
      arbitraryLowPredicateOnCanonicalPath ≡ false

    separateLowSubsetVerifiedRegionProofRequired : Bool
    separateLowSubsetVerifiedRegionProofRequiredIsFalse :
      separateLowSubsetVerifiedRegionProofRequired ≡ false

    plattTrudgianSameCarrierVerifiedRegionTheoremStillRequired : Bool
    plattTrudgianSameCarrierVerifiedRegionTheoremStillRequiredIsTrue :
      plattTrudgianSameCarrierVerifiedRegionTheoremStillRequired ≡ true

    verifiedRegionOrHighCoverStillRequired : Bool
    verifiedRegionOrHighCoverStillRequiredIsTrue :
      verifiedRegionOrHighCoverStillRequired ≡ true

    analyticHighLowRouteCompilesDoubleNegatedRHWithoutStability : Bool
    analyticHighLowRouteCompilesDoubleNegatedRHWithoutStabilityIsTrue :
      analyticHighLowRouteCompilesDoubleNegatedRHWithoutStability ≡ true

    nakedCriticalLineStabilityIsPrimitiveTerminalField : Bool
    nakedCriticalLineStabilityIsPrimitiveTerminalFieldIsFalse :
      nakedCriticalLineStabilityIsPrimitiveTerminalField ≡ false

    exactCriticalLinePredicateRefinementStillRequiredForPositiveRH : Bool
    exactCriticalLinePredicateRefinementStillRequiredForPositiveRHIsTrue :
      exactCriticalLinePredicateRefinementStillRequiredForPositiveRH ≡ true

    criticalLineStabilityCompilesFromRefinement : Bool
    criticalLineStabilityCompilesFromRefinementIsTrue :
      criticalLineStabilityCompilesFromRefinement ≡ true

    theseInputsCompileRiemannHypothesisFor : Bool
    theseInputsCompileRiemannHypothesisForIsTrue :
      theseInputsCompileRiemannHypothesisFor ≡ true

    inputsInhabitedHere : Bool
    inputsInhabitedHereIsFalse : inputsInhabitedHere ≡ false

    unconditionalRHClaimedHere : Bool
    unconditionalRHClaimedHereIsFalse : unconditionalRHClaimedHere ≡ false

    highestAlphaReading : String

canonicalClayTerminalOneLeafBoundary : ClayTerminalOneLeafBoundary
canonicalClayTerminalOneLeafBoundary =
  clay-terminal-one-leaf-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "The prize-facing compiler is now normalized on both sides. High work is one uniform family of independent literal complement-margin cases. Low is definitionally the exact Platt--Trudgian verified-region predicate, so no arbitrary Low carrier or Low-subset theorem remains; only the same-carrier verified-region criticality theorem and verified-region-or-High cover are required. Those analytic/low inputs compile to double-negated RH without critical-line stability. Only the final conversion to positive RH consumes the exact critical-predicate refinement. No substantive input is fabricated here."
