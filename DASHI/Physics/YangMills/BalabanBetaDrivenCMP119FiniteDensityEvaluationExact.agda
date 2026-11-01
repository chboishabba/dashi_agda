module DASHI.Physics.YangMills.BalabanBetaDrivenCMP119FiniteDensityEvaluationExact where

------------------------------------------------------------------------
-- BETA-DRIVEN CMP119 FAMILY WITH SOURCE-FIXED FINITE DENSITY EVALUATION
--
-- One evaluator/application semantics is fixed for the whole literal Round219
-- family.  Every scale-indexed CMP119 complete-density object then inherits the
-- same Section-2 evaluation law.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119Section2FiniteDensityEvaluationExact as SourceEval
import DASHI.Physics.YangMills.BalabanCMP119FiniteDensityAssemblySemanticsExact as Downstream

record BetaDrivenCMP119FiniteDensityEvaluation
    {trajectory split}
    (source :
      Beta.BetaDrivenCompleteDensityInputs
        {trajectory = trajectory} {split = split})
    (family : R219.BetaDrivenCMP119ResidualFamily source)
    (SlowField : Set) : Set₁ where
  field
    evaluateDensity :
      Beta.Density source → SlowField → ℚ

    applyOperationAction :
      R219.Operation family →
      R219.Action family →
      SlowField → ℚ

    assembleDensityEvaluation :
      ∀ operation action slow →
      evaluateDensity
        (R219.assembleDensity family operation action)
        slow
      ≡
      applyOperationAction operation action slow

open BetaDrivenCMP119FiniteDensityEvaluation public

asSection2FiniteDensityEvaluationAt :
  ∀ {trajectory split source family SlowField}
    (semantics :
      BetaDrivenCMP119FiniteDensityEvaluation
        {trajectory = trajectory} {split = split}
        source family SlowField)
    scale →
  SourceEval.CMP119Section2FiniteDensityEvaluation
    (R219.completeDensityAt family scale)
    SlowField
asSection2FiniteDensityEvaluationAt semantics scale = record
  { SourceEval.CMP119Section2FiniteDensityEvaluation.evaluateDensity =
      evaluateDensity semantics
  ; SourceEval.CMP119Section2FiniteDensityEvaluation.applyOperationAction =
      applyOperationAction semantics
  ; SourceEval.CMP119Section2FiniteDensityEvaluation.assembleDensityEvaluation =
      assembleDensityEvaluation semantics
  }

asDownstreamAssemblySemantics :
  ∀ {trajectory split source family SlowField} →
  BetaDrivenCMP119FiniteDensityEvaluation
    {trajectory = trajectory} {split = split}
    source family SlowField →
  Downstream.CMP119FiniteDensityAssemblySemantics
    source family SlowField
asDownstreamAssemblySemantics semantics = record
  { Downstream.CMP119FiniteDensityAssemblySemantics.evaluateDensity =
      evaluateDensity semantics
  ; Downstream.CMP119FiniteDensityAssemblySemantics.applyOperationAction =
      applyOperationAction semantics
  ; Downstream.CMP119FiniteDensityAssemblySemantics.assembleDensityEvaluation =
      assembleDensityEvaluation semantics
  }

selectedDensityEvaluationIsSourceOperationAction :
  ∀ {trajectory split source family SlowField}
    (semantics :
      BetaDrivenCMP119FiniteDensityEvaluation
        {trajectory = trajectory} {split = split}
        source family SlowField)
    cutoff slow →
  evaluateDensity semantics
    (Beta.densityAt source cutoff)
    slow
  ≡
  applyOperationAction semantics
    (R219.operationAt family cutoff)
    (R219.effectiveActionAt family cutoff)
    slow
selectedDensityEvaluationIsSourceOperationAction
  {family = family} semantics cutoff slow =
  SourceEval.sourceDensityEvaluationIsSelectedOperationAction
    (asSection2FiniteDensityEvaluationAt semantics cutoff)
    slow

betaDrivenCMP119FiniteDensityEvaluationCompilerLevel : ProofLevel
betaDrivenCMP119FiniteDensityEvaluationCompilerLevel = machineChecked

betaDrivenCMP119EveryScaleSourceEvaluationLevel : ProofLevel
betaDrivenCMP119EveryScaleSourceEvaluationLevel = machineChecked

betaDrivenCMP119DownstreamAssemblyCompilerLevel : ProofLevel
betaDrivenCMP119DownstreamAssemblyCompilerLevel = machineChecked

-- This is now the sole F1a source-family payment.
literalBetaDrivenCMP119FiniteDensityEvaluationLevel : ProofLevel
literalBetaDrivenCMP119FiniteDensityEvaluationLevel = conditional
