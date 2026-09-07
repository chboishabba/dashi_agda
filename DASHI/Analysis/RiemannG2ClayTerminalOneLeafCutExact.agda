module DASHI.Analysis.RiemannG2ClayTerminalOneLeafCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannPlattTrudgianLowCompletionAdapterExact as Low
import DASHI.Analysis.RiemannG2UniformIndependentComplementHighProducerExact as High
import DASHI.Analysis.RiemannCriticalLineStabilityRefinementExact as Stability

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
-- The old naked `CriticalLineStable` assumption is no longer a primitive field
-- of this terminal input.  It is compiler output from S.
--
-- H is the only remaining high-side scalar analytic family.  Its per-case heart
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

    criticalLineRefinement :
      Stability.CriticalLinePredicateRefinement analytic

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

compiledCriticalLineStable :
  forall {analytic} ->
  (input : ClayTerminalOneLeafInput analytic) ->
  Universal.CriticalLineStable analytic
compiledCriticalLineStable input =
  Stability.compileCriticalLineStable (criticalLineRefinement input)

compiledHighCritical :
  forall {analytic} ->
  (input : ClayTerminalOneLeafInput analytic) ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  HighRegion input rho ->
  Universal.analyticCritical rho
compiledHighCritical input =
  High.highCriticalFromIndependentComplement
    (compiledCriticalLineStable input)
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

    nakedCriticalLineStabilityIsPrimitiveTerminalField : Bool
    nakedCriticalLineStabilityIsPrimitiveTerminalFieldIsFalse :
      nakedCriticalLineStabilityIsPrimitiveTerminalField ≡ false

    exactCriticalLinePredicateRefinementStillRequired : Bool
    exactCriticalLinePredicateRefinementStillRequiredIsTrue :
      exactCriticalLinePredicateRefinementStillRequired ≡ true

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
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "The prize-facing compiler is direct and allowance-free. Low-side work is one exact Platt--Trudgian verified-region transport plus the Low/High cover. High-side scalar work is one uniform family of independent literal complement-margin cases, each compiling directly through the split-complement contradiction. The previous naked CriticalLineStable premise is removed from the canonical input: instead identify the abstract completed-zeta criticalLine predicate with an exact stable refinement, from which stability compiles constructively. Separate finite-near/Gamma envelope APIs, payment records and consumer-assigned allowances are not canonical prerequisites. Given these same-substrate inputs, RiemannHypothesisFor is compiler output. None is fabricated here, so no unconditional RH theorem is claimed."
