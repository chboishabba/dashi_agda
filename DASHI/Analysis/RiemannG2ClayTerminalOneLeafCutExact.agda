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
-- All assembly below is exact and the canonical route is allowance-free.
-- The full same-substrate RH theorem needs:
--
--   L. one exact Platt--Trudgian low-region transport on the chosen Low part;
--   H. for every chosen High zero assumed off-line, one direct independent
--      literal complement-margin case;
--   C. a cover saying every nontrivial zero is Low or High;
--   S. stability of the critical-line predicate under double negation.
--
-- H is the only remaining high-side analytic family.  Its per-case scalar heart
-- is the one-leaf inequality
--
--   cast(D_near(J)+B_far(J)) + cast(D_Gamma(g_pole)) < cast(M_cluster),
--
-- proved independently of the final cluster balance.  The direct high case goes
-- straight through SplitPoleQuotientComplementMargin to bottom.  No allowance,
-- payment, analytic-core, or further contradiction theorem sits after H.
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

compiledHighCritical :
  forall {analytic} ->
  (input : ClayTerminalOneLeafInput analytic) ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  HighRegion input rho ->
  Universal.analyticCritical rho
compiledHighCritical input =
  High.highCriticalFromIndependentComplement
    (criticalLineStable input)
    (highProducer input)

compiledAnalyticHighLowCompletion :
  forall {analytic} ->
  (input : ClayTerminalOneLeafInput analytic) ->
  Universal.AnalyticHighLowCompletion analytic
compiledAnalyticHighLowCompletion input =
  Universal.analytic-high-low-completion
    (LowRegion input)
    (HighRegion input)
    (lowHighCover input)
    (compiledLowCritical input)
    (compiledHighCritical input)

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
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "The prize-facing compiler is now direct and allowance-free. Low-side work is one exact Platt--Trudgian verified-region transport plus the Low/High cover. High-side work is one uniform family of independent literal complement-margin cases, each compiling directly through the split-complement contradiction. Separate finite-near/Gamma envelope APIs, producer/payment records, and the consumer-assigned allowance layer are not on the canonical path. Critical-line stability remains the existing logical/interface receipt. Given these same-substrate inputs, RiemannHypothesisFor is compiler output. None is fabricated here, so no unconditional RH theorem is claimed."
