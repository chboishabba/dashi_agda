module DASHI.Biology.IIT4SymbolicScalarBackendExact where

open import DASHI.Core.Prelude

import DASHI.Biology.IIT4FiniteProbabilityRepertoireExact as Prob
import DASHI.Biology.IIT4SystemPhiInputExact as Phi

------------------------------------------------------------------------
-- SYMBOLIC IIT SCALAR BACKEND
--
-- Keep the source-faithful equation shape executable even when the analytic
-- logarithm is not yet evaluated in Agda.  The AST below is not a numerical
-- approximation: it retains the exact rational inputs to |log(p/q)|_+, the
-- selectivity weighting, cause/effect minimum and partition normalisation.
------------------------------------------------------------------------

data SymbolicScore : Set where
  positiveLogRatioTerm :
    Prob.ProbabilityFraction →
    Prob.ProbabilityFraction →
    SymbolicScore
  probabilityWeightedTerm :
    Prob.ProbabilityFraction → SymbolicScore → SymbolicScore
  minimumTerm : SymbolicScore → SymbolicScore → SymbolicScore
  normalizedTerm : SymbolicScore → Nat → SymbolicScore

record SymbolicOrder (left right : SymbolicScore) : Set where
  constructor symbolicOrder
  field
    orderReceipt : String

open SymbolicOrder public

symbolicBackend : Phi.IntrinsicInformationScalarBackend
symbolicBackend =
  Phi.intrinsicInformationScalarBackend
    SymbolicScore
    positiveLogRatioTerm
    probabilityWeightedTerm
    minimumTerm
    normalizedTerm
    SymbolicOrder
    "exact symbolic IIT equation tree; numerical log/order requires a proved analytic interpretation"

symbolicIntegratedSide :
  (input : Phi.ProbabilityLossInput) →
  Phi.integratedSideScore symbolicBackend input ≡
  probabilityWeightedTerm
    (Phi.selectivityWeight input)
    (positiveLogRatioTerm
      (Phi.unpartitionedConditional input)
      (Phi.partitionedConditional input))
symbolicIntegratedSide input = refl

symbolicSystemPhiAtPartition :
  ∀ {system}
    (input : Phi.CauseEffectPartitionInput system) →
  Phi.systemPhiAtPartition symbolicBackend input ≡
  minimumTerm
    (probabilityWeightedTerm
      (Phi.selectivityWeight (Phi.causeLoss input))
      (positiveLogRatioTerm
        (Phi.unpartitionedConditional (Phi.causeLoss input))
        (Phi.partitionedConditional (Phi.causeLoss input))))
    (probabilityWeightedTerm
      (Phi.selectivityWeight (Phi.effectLoss input))
      (positiveLogRatioTerm
        (Phi.unpartitionedConditional (Phi.effectLoss input))
        (Phi.partitionedConditional (Phi.effectLoss input))))
symbolicSystemPhiAtPartition input = refl

record SymbolicScalarBoundary : Set where
  constructor symbolicScalarBoundary
  field
    preservesExactProbabilityInputs : Bool
    preservesPositiveLogRatioShape : Bool
    preservesSelectivityWeighting : Bool
    preservesCauseEffectMinimum : Bool
    preservesPartitionNormalisation : Bool
    symbolicASTIsNumericalLogEvaluation : Bool
    analyticInterpretationStillRequiresProof : Bool

open SymbolicScalarBoundary public

canonicalSymbolicScalarBoundary : SymbolicScalarBoundary
canonicalSymbolicScalarBoundary =
  symbolicScalarBoundary
    true true true true true false true

symbolicDoesNotPretendToEvaluateLog :
  symbolicASTIsNumericalLogEvaluation canonicalSymbolicScalarBoundary ≡ false
symbolicDoesNotPretendToEvaluateLog = refl
