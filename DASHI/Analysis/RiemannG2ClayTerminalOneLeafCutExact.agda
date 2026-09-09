module DASHI.Analysis.RiemannG2ClayTerminalOneLeafCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannPlattTrudgianCanonicalLowRegionExact as Low
import DASHI.Analysis.RiemannG2UniformLiteralPhaseHighProducerExact as High
import DASHI.Analysis.RiemannCriticalLineStabilityRefinementExact as Stability
import DASHI.Analysis.RiemannG2ConstructiveNegativeRHCompletionExact as Negative

------------------------------------------------------------------------
-- CLAY-FACING TERMINAL CUT
--
-- The public high-side input is now the lowest theorem-bearing surface reached
-- by introspection: for every arbitrary High zero assumed off-line, supply one
-- exact literal finite-near model, one unpaid final representation context, and
-- the independent phase-visible
--
--   literalNear + transportedFar + Gamma < clusterMargin
--
-- theorem.  The legacy opaque combined-margin producer is compiler output.
--
-- Low is definitionally the Platt--Trudgian verified region.  Low + literal High
-- + cover compile first to constructive double-negated RH.  The exact critical
-- predicate refinement is consumed only in the final conversion to positive RH.
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
      High.UniformLiteralPhaseHighProducer analytic HighRegion

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

    extraHighOrdinatePaymentAfterUniformLiteralPhaseProducer : Bool
    extraHighOrdinatePaymentAfterUniformLiteralPhaseProducerIsFalse :
      extraHighOrdinatePaymentAfterUniformLiteralPhaseProducer ≡ false

    separateNearEnvelopePrimitiveLeaf : Bool
    separateNearEnvelopePrimitiveLeafIsFalse :
      separateNearEnvelopePrimitiveLeaf ≡ false

    separateGammaEnvelopePrimitiveLeaf : Bool
    separateGammaEnvelopePrimitiveLeafIsFalse :
      separateGammaEnvelopePrimitiveLeaf ≡ false

    uniformLiteralPhaseJointMarginIsHighAnalyticFamily : Bool
    uniformLiteralPhaseJointMarginIsHighAnalyticFamilyIsTrue :
      uniformLiteralPhaseJointMarginIsHighAnalyticFamily ≡ true

    opaqueCanonicalMarginProducerPrimitiveAtClayBoundary : Bool
    opaqueCanonicalMarginProducerPrimitiveAtClayBoundaryIsFalse :
      opaqueCanonicalMarginProducerPrimitiveAtClayBoundary ≡ false

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
    "The prize-facing compiler now exposes the literal phase theorem family itself. High work is: for every arbitrary high off-line zero, provide the exact final near phase model, unpaid same-object context, and independent literalNear+far+Gamma<cluster margin. The opaque canonical-margin producer is downstream compiler output. Low is definitionally the exact Platt--Trudgian verified region, so no arbitrary Low carrier or Low-subset theorem remains. These inputs compile to double-negated RH without stability; only the final positive-RH conversion consumes the exact critical-predicate refinement. No substantive theorem is fabricated here."
