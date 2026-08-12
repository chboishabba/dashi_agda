module DASHI.Cognition.PNF.RuntimeThroughputConstitution where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

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
    inputUnits : Nat
    outputUnits : Nat
    workUnits : Nat
    elapsedUnits : Nat
    peakMemoryUnits : Nat

open StageCostReceipt public

------------------------------------------------------------------------
-- Explicit affine-work envelope.
--
-- The semantic unit is application-selected: tokens, demands, bounded
-- candidates, interface rows, or another measured carrier.  This receipt is
-- the formal place to reject hidden quadratic/superlinear materialisation when
-- the runtime claims a stage is work-bounded by its chosen carrier.
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
-- Corpus/archive scale receipt.
--
-- This does not assert that all semantic algorithms are globally linear.  It
-- records an explicit measured work envelope relative to the carrier that the
-- implementation claims should control the stage.  If a pairwise surface is
-- necessary, it must first be represented in that carrier or separately
-- bounded before materialisation.
------------------------------------------------------------------------

record ArchiveScaleReceipt : Set where
  constructor archiveScaleReceipt
  field
    representedCarrierUnits : Nat
    measuredPostParserWorkUnits : Nat
    envelopeSlope : Nat
    envelopeIntercept : Nat
    postParserWorkWithinDeclaredEnvelope :
      measuredPostParserWorkUnits
      ≤ᶜ ((envelopeSlope *ᶜ representedCarrierUnits) +ᶜ envelopeIntercept)

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
    performanceReceiptCannotPromoteSemantics
