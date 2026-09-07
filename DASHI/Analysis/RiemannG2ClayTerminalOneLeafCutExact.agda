module DASHI.Analysis.RiemannG2ClayTerminalOneLeafCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannPlattTrudgianLowCompletionAdapterExact as Low
import DASHI.Analysis.RiemannG2UniformIndependentComplementHighProducerExact as High
import DASHI.Analysis.RiemannCriticalLineStabilityRefinementExact as Stability
import DASHI.Analysis.RiemannG2ConstructiveNegativeRHCompletionExact as Negative

------------------------------------------------------------------------
-- CLAY-FACING TERMINAL CUT
--
-- All assembly below is exact and the canonical route is allowance-free.
-- The full same-substrate RH theorem needs:
--
--   L. one exact Platt--Trudgian low-region transport on the chosen Low part;
--   H. for every chosen High zero assumed off-line, one direct independent
--      literal complement-margin case;
--   C. a cover saying every nontrivial zero is Low or High;
--   S. an exact refinement of the abstract completed-zeta criticalLine
--      predicate to a concrete stable predicate.
--
-- L+H+C compile first to constructive double-negated RH.  S is used only in the
-- final logical conversion to positive prize-facing RH.  Thus stability is no
-- longer entangled with the harmonic-analysis producer.
--
-- H is the only remaining high-side scalar analytic family.  Its per-case heart
-- is the one-leaf inequality
--
--   cast(D_near(J)+B_far(J)) + cast(D_Gamma(g_pole)) < cast(M_cluster),
--
-- proved independently of the final cluster balance.
------------------------------------------------------------------------

record ClayTerminalOneLeafInput
    (analytic : Analytic.AnalyticSubstrate) : Set₁ where
  field
    LowRegion HighRegion : Universal.AnalyticNontrivialZero analytic -> Set

    lowHighCover :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      LowRegion rho ⊎ HighRegion rho

    lowTransport :
      Low.PlattTrudgianLowCriticalityTransport analytic LowRegion

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
  { Negative.LowRegion = LowRegion input
  ; Negative.HighRegion = HighRegion input
  ; Negative.lowHighCover = lowHighCover input
  ; Negative.lowTransport = lowTransport input
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

    plattTrudgianLowTransportStillRequired : Bool
    plattTrudgianLowTransportStillRequiredIsTrue :
      plattTrudgianLowTransportStillRequired ≡ true

    lowHighCoverStillRequired : Bool
    lowHighCoverStillRequiredIsTrue :
      lowHighCoverStillRequired ≡ true

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
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "The prize-facing compiler is direct and allowance-free. Low verified-region transport, the Low/High cover, and the uniform high contradiction compile first to double-negated RH with no critical-line stability assumption. Only the final conversion to positive RH consumes the exact critical-predicate refinement. The high scalar work remains one uniform family of independent literal complement-margin cases. Separate finite-near/Gamma envelope APIs, payment records and consumer-assigned allowances are not canonical prerequisites. None of the substantive inputs is fabricated here, so no unconditional RH theorem is claimed."
