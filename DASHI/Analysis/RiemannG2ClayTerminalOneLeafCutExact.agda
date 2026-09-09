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
-- High is now the literal phase theorem family itself.  For every arbitrary
-- High zero assumed off-line:
--
--   exact final-near literal model
--   + balance-free actual-ClusterResponse context
--   + literalNear + transportedFar + Gamma < ClusterResponse
--   + downstream final balance
--   -> contradiction.
--
-- The analytic payment cannot access cluster = Off + Gamma through its context.
-- No intermediate M_cluster or M_cluster <= ClusterResponse theorem is primitive.
-- Low remains definitionally the Platt--Trudgian verified region; high+low compile
-- first to double-negated RH, and the exact critical-predicate refinement is used
-- only in the final positive-RH conversion.
------------------------------------------------------------------------

record ClayTerminalOneLeafInput
    (analytic : Analytic.AnalyticSubstrate) : Set₁ where
  field
    lowTransport : Low.PlattTrudgianVerifiedRegionTransport analytic
    HighRegion : Universal.AnalyticNontrivialZero analytic -> Set
    verifiedOrHighCover :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      Low.CanonicalLowRegion lowTransport rho ⊎ HighRegion rho
    highProducer : High.UniformLiteralPhaseHighProducer analytic HighRegion
    criticalLineRefinement : Stability.CriticalLinePredicateRefinement analytic
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
    "The prize-facing compiler exposes the literal high theorem family itself. For every arbitrary high off-line zero, provide the exact final-near model, a balance-free actual ClusterResponse context, and independently prove literalNear+far+Gamma<ClusterResponse. The final cluster=Off+Gamma equality is downstream only. No intermediate M_cluster or M_cluster<=ClusterResponse theorem, arbitrary Low carrier, Low-subset theorem, allowance layer, or naked critical-line stability is primitive. These inputs compile to double-negated RH before the final critical-predicate refinement. RH is not derived here."
