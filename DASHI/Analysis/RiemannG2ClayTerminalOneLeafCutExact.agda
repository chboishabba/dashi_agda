module DASHI.Analysis.RiemannG2ClayTerminalOneLeafCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannPlattTrudgianLowCompletionAdapterExact as Low
import DASHI.Analysis.RiemannG2UniformIndependentComplementHighProducerExact as High

------------------------------------------------------------------------
-- CLAY-FACING TERMINAL CUT
--
-- All assembly below is now exact.  The full same-substrate RH theorem needs:
--
--   L. one exact Platt--Trudgian low-region transport on the chosen Low part;
--   H. for every chosen High zero assumed off-line, one independent literal
--      complement-margin case;
--   C. a cover saying every nontrivial zero is Low or High;
--   S. stability of the critical-line predicate under double negation.
--
-- H is the only remaining high-side analytic family.  Its per-case scalar heart
-- is the one-leaf inequality
--
--   cast(D_near(J)+B_far(J)) + cast(D_Gamma(g_pole)) < cast(M_cluster),
--
-- proved independently of the final cluster balance.  No hidden payment or
-- contradiction theorem sits after H.
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

    criticalLineStable : Universal.CriticalLineStable analytic

    highProducer :
      High.UniformIndependentComplementHighProducer analytic HighRegion

    terminalReference : String

open ClayTerminalOneLeafInput public

compiledLowCritical :
  forall {analytic} ->
  (input : ClayTerminalOneLeafInput analytic) ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  LowRegion input rho ->
  Universal.analyticCritical rho
compiledLowCritical input =
  Low.compileLowCertifiedCritical (lowTransport input)

compiledHighProducer :
  forall {analytic} ->
  (input : ClayTerminalOneLeafInput analytic) ->
  Universal.HighOffLineAnalyticCoreProducer analytic (HighRegion input)
compiledHighProducer input =
  High.compileUniformHighProducer (highProducer input)

compiledAnalyticHighLowCompletion :
  forall {analytic} ->
  (input : ClayTerminalOneLeafInput analytic) ->
  Universal.AnalyticHighLowCompletion analytic
compiledAnalyticHighLowCompletion {analytic} input =
  Universal.compileAnalyticHighLowCompletion
    analytic
    (LowRegion input)
    (HighRegion input)
    (lowHighCover input)
    (compiledLowCritical input)
    (criticalLineStable input)
    (compiledHighProducer input)

compileClayTerminalOneLeafToRH :
  forall {analytic} ->
  ClayTerminalOneLeafInput analytic ->
  Analytic.RiemannHypothesisFor analytic
compileClayTerminalOneLeafToRH {analytic} input =
  Universal.analyticHighLowCompletionImpliesRH
    analytic
    (compiledAnalyticHighLowCompletion input)

------------------------------------------------------------------------
-- BOUNDARY
------------------------------------------------------------------------

record ClayTerminalOneLeafBoundary : Set where
  constructor clay-terminal-one-leaf-boundary
  field
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

    criticalLineStabilityStillRequired : Bool
    criticalLineStabilityStillRequiredIsTrue :
      criticalLineStabilityStillRequired ≡ true

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
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "The prize-facing compiler is now explicit. Low-side work is one exact Platt--Trudgian verified-region transport plus the Low/High cover. High-side work is one uniform family of independent literal complement-margin cases; separate finite-near and Gamma envelope APIs are not primitive leaves. Critical-line stability is a logical/interface receipt already exposed by the existing Weil-square separator architecture. Given these inputs on the same AnalyticSubstrate, RiemannHypothesisFor is compiler output. None of the required inputs is fabricated here, so no unconditional RH theorem is claimed."
