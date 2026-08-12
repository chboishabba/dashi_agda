module DASHI.Cognition.PNF.RuntimeThroughputConstitution where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Cognition.PNF.ComplexityArithmetic

------------------------------------------------------------------------
-- Runtime performance receipts.
--
-- These are empirical contracts to be populated from Python/PostgreSQL
-- measurements.  Agda does not claim a particular database plan, machine,
-- parser throughput or asymptotic bound without such a receipt.
------------------------------------------------------------------------

record StageCostReceipt : Set where
  constructor stageCostReceipt
  field
    workloadId : String
    inputUnits : Nat
    outputUnits : Nat
    workUnits : Nat
    elapsedUnits : Nat
    peakMemoryUnits : Nat

open StageCostReceipt public

------------------------------------------------------------------------
-- Explicit affine-work point receipt.
--
-- The semantic unit is application-selected: tokens, demands, bounded
-- candidates, interface rows, or another measured carrier.  One observation
-- only certifies one point; archive-scale claims use the non-empty series below.
------------------------------------------------------------------------

record AffineWorkReceipt (stage : StageCostReceipt) : Set where
  constructor affineWorkReceipt
  field
    slope : Nat
    intercept : Nat
    workWithinAffineEnvelope :
      workUnits stage
      ≤ᶜ ((slope *ᶜ inputUnits stage) +ᶜ intercept)

open AffineWorkReceipt public

------------------------------------------------------------------------
-- Parser-dominance target.
--
-- The design objective is that post-parser semantics become sufficiently cheap
-- that spaCy remains the dominant expensive stage.  The target factor is a
-- runtime policy, not fixed here.
------------------------------------------------------------------------

record ParserDominanceTarget : Set where
  constructor parserDominanceTarget
  field minimumDominanceFactor : Nat

open ParserDominanceTarget public

record ParserDominatedOptimisationReceipt
    (target : ParserDominanceTarget) : Set where
  constructor parserDominatedOptimisationReceipt
  field
    parserBefore : StageCostReceipt
    parserAfter : StageCostReceipt
    postParserAfter : StageCostReceipt
    observedDominanceFactor : Nat

    -- Comparisons only mean anything for the same corpus/document workload.
    sameParserWorkload :
      workloadId parserBefore ≡ workloadId parserAfter
    samePostParserWorkload :
      workloadId parserAfter ≡ workloadId postParserAfter

    -- We do not earn parser dominance by deliberately making the parser worse.
    parserElapsedNotIncreased :
      elapsedUnits parserAfter ≤ᶜ elapsedUnits parserBefore
    parserWorkNotIncreased :
      workUnits parserAfter ≤ᶜ workUnits parserBefore

    dominanceTargetMet :
      minimumDominanceFactor target ≤ᶜ observedDominanceFactor

    postParserElapsedDominated :
      (observedDominanceFactor *ᶜ elapsedUnits postParserAfter)
      ≤ᶜ elapsedUnits parserAfter

    postParserWorkDominated :
      (observedDominanceFactor *ᶜ workUnits postParserAfter)
      ≤ᶜ workUnits parserAfter

open ParserDominatedOptimisationReceipt public

------------------------------------------------------------------------
-- Non-empty archive/corpus scaling series.
------------------------------------------------------------------------

record ScalePoint : Set where
  constructor scalePoint
  field
    scaleWorkloadId : String
    representedCarrierUnits : Nat
    measuredPostParserWorkUnits : Nat
    measuredElapsedUnits : Nat
    measuredPeakMemoryUnits : Nat

open ScalePoint public

data AllWithinAffine
    (slope intercept : Nat) : List ScalePoint → Set where
  affineNil : AllWithinAffine slope intercept []
  affineCons :
    ∀ {point rest} →
    measuredPostParserWorkUnits point
      ≤ᶜ ((slope *ᶜ representedCarrierUnits point) +ᶜ intercept) →
    AllWithinAffine slope intercept rest →
    AllWithinAffine slope intercept (point ∷ rest)

record ArchiveScaleReceipt : Set where
  constructor archiveScaleReceipt
  field
    firstObservation : ScalePoint
    remainingObservations : List ScalePoint
    envelopeSlope : Nat
    envelopeIntercept : Nat
    allObservedPointsWithinDeclaredEnvelope :
      AllWithinAffine
        envelopeSlope
        envelopeIntercept
        (firstObservation ∷ remainingObservations)

open ArchiveScaleReceipt public

------------------------------------------------------------------------
-- Performance has no semantic authority.
------------------------------------------------------------------------

data PerformanceSemanticPromotionPermission : Set where

performanceReceiptCannotPromoteSemantics :
  PerformanceSemanticPromotionPermission → ⊥
performanceReceiptCannotPromoteSemantics ()

record RuntimeThroughputBoundary : Set where
  constructor runtimeThroughputBoundary
  field
    parserDominanceIsEmpiricalContract : Bool
    parserDominanceIsEmpiricalContractIsTrue :
      parserDominanceIsEmpiricalContract ≡ true
    parserMayBeArtificiallySlowedToMeetTarget : Bool
    parserMayBeArtificiallySlowedToMeetTargetIsFalse :
      parserMayBeArtificiallySlowedToMeetTarget ≡ false
    singleBenchmarkPointProvesScaling : Bool
    singleBenchmarkPointProvesScalingIsFalse :
      singleBenchmarkPointProvesScaling ≡ false
    unboundedIntermediateWorkMayHideBehindBoundedOutput : Bool
    unboundedIntermediateWorkMayHideBehindBoundedOutputIsFalse :
      unboundedIntermediateWorkMayHideBehindBoundedOutput ≡ false
    runtimePerformanceMayPromoteSemanticTruth : Bool
    runtimePerformanceMayPromoteSemanticTruthIsFalse :
      runtimePerformanceMayPromoteSemanticTruth ≡ false
    performanceHasNoSemanticPermission :
      PerformanceSemanticPromotionPermission → ⊥

open RuntimeThroughputBoundary public

canonicalRuntimeThroughputBoundary : RuntimeThroughputBoundary
canonicalRuntimeThroughputBoundary =
  runtimeThroughputBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    performanceReceiptCannotPromoteSemantics
