module DASHI.Statistics.DirectionalInferenceDesignExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import DASHI.Algebra.Trit using (neg; zer; pos)

import DASHI.Core.ExperimentalCoordinateDesignExact as Experiment
import DASHI.Statistics.DirectionalEvidenceTritExact as Evidence

------------------------------------------------------------------------
-- DIRECTIONAL INFERENCE DESIGN
--
-- A statistical / experimental result may be interpreted directionally only
-- relative to an explicit design and an explicit interpretation rule.  This
-- prevents a test decision such as `failToReject` from being silently promoted
-- into evidence for the opposite scientific proposition.
------------------------------------------------------------------------

record DirectionalInferenceDesign
    (World Control Value Dimension Result Hypothesis : Set) : Set₁ where
  constructor directional-inference-design
  field
    experimentDesign :
      Experiment.ExperimentalCoordinateDesign World Control Value Dimension

    semantics : Evidence.DirectionalEvidenceSemantics Result Hypothesis

    PositiveRegion : Result → Hypothesis → Set
    NegativeRegion : Result → Hypothesis → Set
    UnderdeterminedRegion : Result → Hypothesis → Set

    positiveRegionSound :
      ∀ {result hypothesis} →
      PositiveRegion result hypothesis →
      Evidence.SupportsPositive semantics result hypothesis

    negativeRegionSound :
      ∀ {result hypothesis} →
      NegativeRegion result hypothesis →
      Evidence.SupportsNegative semantics result hypothesis

    underdeterminedRegionSound :
      ∀ {result hypothesis} →
      UnderdeterminedRegion result hypothesis →
      Evidence.Underdetermined semantics result hypothesis

    hypothesisReference : Hypothesis → String
    decisionRuleReference : String
    calibrationReference : String
    nuisanceHandlingReference : String

open DirectionalInferenceDesign public

------------------------------------------------------------------------
-- Positive and negative interpretations are proof-bearing receipts.  Neither
-- can be obtained merely from failure of the opposite direction.
------------------------------------------------------------------------

record PositiveEvidenceReceipt
    {World Control Value Dimension Result Hypothesis : Set}
    (design : DirectionalInferenceDesign
      World Control Value Dimension Result Hypothesis)
    (result : Result)
    (hypothesis : Hypothesis) : Set₁ where
  constructor positive-evidence-receipt
  field
    inPositiveRegion : PositiveRegion design result hypothesis

open PositiveEvidenceReceipt public

record NegativeEvidenceReceipt
    {World Control Value Dimension Result Hypothesis : Set}
    (design : DirectionalInferenceDesign
      World Control Value Dimension Result Hypothesis)
    (result : Result)
    (hypothesis : Hypothesis) : Set₁ where
  constructor negative-evidence-receipt
  field
    inNegativeRegion : NegativeRegion design result hypothesis

open NegativeEvidenceReceipt public

record UnderdeterminedEvidenceReceipt
    {World Control Value Dimension Result Hypothesis : Set}
    (design : DirectionalInferenceDesign
      World Control Value Dimension Result Hypothesis)
    (result : Result)
    (hypothesis : Hypothesis) : Set₁ where
  constructor underdetermined-evidence-receipt
  field
    inUnderdeterminedRegion : UnderdeterminedRegion design result hypothesis

open UnderdeterminedEvidenceReceipt public

positiveReceiptDisposition :
  ∀ {World Control Value Dimension Result Hypothesis : Set}
    {design : DirectionalInferenceDesign
      World Control Value Dimension Result Hypothesis}
    {result : Result} {hypothesis : Hypothesis} →
  PositiveEvidenceReceipt design result hypothesis →
  Evidence.DirectionalEvidenceDisposition
    (semantics design) result hypothesis pos
positiveReceiptDisposition receipt =
  Evidence.positiveEvidence
    (positiveRegionSound _ (inPositiveRegion receipt))

negativeReceiptDisposition :
  ∀ {World Control Value Dimension Result Hypothesis : Set}
    {design : DirectionalInferenceDesign
      World Control Value Dimension Result Hypothesis}
    {result : Result} {hypothesis : Hypothesis} →
  NegativeEvidenceReceipt design result hypothesis →
  Evidence.DirectionalEvidenceDisposition
    (semantics design) result hypothesis neg
negativeReceiptDisposition receipt =
  Evidence.negativeEvidence
    (negativeRegionSound _ (inNegativeRegion receipt))

underdeterminedReceiptDisposition :
  ∀ {World Control Value Dimension Result Hypothesis : Set}
    {design : DirectionalInferenceDesign
      World Control Value Dimension Result Hypothesis}
    {result : Result} {hypothesis : Hypothesis} →
  UnderdeterminedEvidenceReceipt design result hypothesis →
  Evidence.DirectionalEvidenceDisposition
    (semantics design) result hypothesis zer
underdeterminedReceiptDisposition receipt =
  Evidence.unresolvedEvidence
    (underdeterminedRegionSound _ (inUnderdeterminedRegion receipt))

------------------------------------------------------------------------
-- Test-decision adapter boundary.  This record is intentionally generic rather
-- than importing one concrete statistics implementation: a decision procedure
-- must separately state which, if any, directional evidence receipt it earns.
------------------------------------------------------------------------

record DecisionInterpretationBoundary : Set where
  constructor decision-interpretation-boundary
  field
    failToRejectAutomaticallySupportsOpposite : Bool
    rejectingOneNullAutomaticallyProvesEveryOppositeClaim : Bool
    directionalMeaningDependsOnDeclaredHypothesis : Bool
    nuisanceAndCalibrationRemainSeparateCoordinates : Bool

canonicalDecisionInterpretationBoundary : DecisionInterpretationBoundary
canonicalDecisionInterpretationBoundary =
  decision-interpretation-boundary false false true true
