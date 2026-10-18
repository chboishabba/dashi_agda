module DASHI.Physics.YangMills.BalabanCMP119Equation171WeightedStepApproximationExact where

------------------------------------------------------------------------
-- CMP119 ONE-STEP T FACTOR -> HAAR-WEIGHTED EQ.(1.71) APPROXIMATION
--
-- For every source (sequence, component, ordered step):
--
--   source oneStepValue
--     = literal Eq.(1.71) source T-mass
--
-- and the refinement-n approximation is the corresponding Haar-weighted
-- Gate4 quadrature.  The marked error is then exactly bounded by that slice's
-- tagged oscillation modulus.
--
-- Feeding this adapter into BalabanCMP119FactorizedDensityApproximationExact
-- propagates the local Eq.(1.71) errors through (2.20), (2.19), and (2.18).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; absℝ; _-ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119Equation218FactorizedFunctionalDensityExact as Factor
import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityApproximationExact as Approx
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanCMP122Equation171WeightedGate4RefinementLimitExact as Weighted
import DASHI.Physics.YangMills.BalabanCMP122Equation171WeightedGate4QuadratureSliceExact as Slice
import DASHI.Physics.YangMills.BalabanCompactHaarMassExactTaggedPartitionExact as Tagged
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

record CMP119Equation171WeightedStepApproximation
    {trajectory split SlowField Sequence Component Step}
    (factorized :
      Factor.CMP119Equation218FactorizedFunctionalData
        {trajectory = trajectory} {split = split}
        SlowField Sequence Component Step)
    {Scale Fine FunctionalValue : Set}
    (embedding :
      RingEmbed.RationalRealRingEmbedding)
    (sequenceLimit :
      Seq.RealSequenceLimitByVanishingError) : Set₂ where
  field
    sourceTAt :
      Sequence → Component → Step →
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField

    quadratureAt :
      (sequence : Sequence) →
      (component : Component) →
      (step : Step) →
      Weighted.Equation171WeightedGate4RefinementLimit
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = FunctionalValue}
        (sourceTAt sequence component step) embedding sequenceLimit

    sourceStepIsEquation171Mass :
      ∀ scale sequence component step slow →
      Factor.oneStepValue factorized
        scale sequence component step slow
      ≡
      Eq171.sourceTOperationMass
        (sourceTAt sequence component step)
        scale slow

    ordinaryMajorant :
      Nat → Sequence → Component → Step → SlowField → ℝ

    ordinaryNonnegative :
      ∀ scale sequence component step slow →
      0ℝ ≤ℝ ordinaryMajorant
        scale sequence component step slow

    sourceStepBound :
      ∀ scale sequence component step slow →
      absℝ
        (Factor.oneStepValue factorized
          scale sequence component step slow)
      ≤ℝ ordinaryMajorant
        scale sequence component step slow

    approximateStepBound :
      ∀ refinement scale sequence component step slow →
      absℝ
        (Weighted.weightedGate4MassAt
          (quadratureAt sequence component step)
          refinement scale slow)
      ≤ℝ ordinaryMajorant
        scale sequence component step slow

    residualMajorant :
      Nat → Sequence → SlowField → ℝ

    residualMajorantNonnegative :
      ∀ scale sequence slow →
      0ℝ ≤ℝ residualMajorant scale sequence slow

    residualBound :
      ∀ scale sequence slow →
      absℝ (Factor.sequenceResidual factorized
        scale sequence slow)
      ≤ℝ residualMajorant scale sequence slow

open CMP119Equation171WeightedStepApproximation public

markedMajorant :
  ∀ {trajectory split SlowField Sequence Component Step factorized
      Scale Fine FunctionalValue embedding sequenceLimit} →
  CMP119Equation171WeightedStepApproximation
    {trajectory = trajectory} {split = split}
    {SlowField = SlowField} {Sequence = Sequence}
    {Component = Component} {Step = Step}
    factorized
    {Scale = Scale} {Fine = Fine} {FunctionalValue = FunctionalValue}
    embedding sequenceLimit →
  Nat → Nat → Sequence → Component → Step → SlowField → ℝ
markedMajorant dataSet refinement scale sequence component step slow =
  Tagged.modulus
    (Slice.taggedAt
      (Weighted.sliceAt
        (quadratureAt dataSet sequence component step)
        refinement)
      scale slow)

markedMajorantNonnegative :
  ∀ {trajectory split SlowField Sequence Component Step factorized
      Scale Fine FunctionalValue embedding sequenceLimit}
    (dataSet :
      CMP119Equation171WeightedStepApproximation
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField} {Sequence = Sequence}
        {Component = Component} {Step = Step}
        factorized
        {Scale = Scale} {Fine = Fine} {FunctionalValue = FunctionalValue}
        embedding sequenceLimit)
    refinement scale sequence component step slow →
  0ℝ ≤ℝ markedMajorant
    dataSet refinement scale sequence component step slow
markedMajorantNonnegative dataSet refinement scale sequence component step slow =
  Tagged.modulusNonnegative
    (Slice.taggedAt
      (Weighted.sliceAt
        (quadratureAt dataSet sequence component step)
        refinement)
      scale slow)

sourceStepToWeightedQuadratureError :
  ∀ {trajectory split SlowField Sequence Component Step factorized
      Scale Fine FunctionalValue embedding sequenceLimit}
    (dataSet :
      CMP119Equation171WeightedStepApproximation
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField} {Sequence = Sequence}
        {Component = Component} {Step = Step}
        factorized
        {Scale = Scale} {Fine = Fine} {FunctionalValue = FunctionalValue}
        embedding sequenceLimit)
    refinement scale sequence component step slow →
  absℝ
    (Factor.oneStepValue factorized
      scale sequence component step slow
      -ℝ
     Weighted.weightedGate4MassAt
       (quadratureAt dataSet sequence component step)
       refinement scale slow)
  ≤ℝ
  markedMajorant
    dataSet refinement scale sequence component step slow
sourceStepToWeightedQuadratureError
  dataSet refinement scale sequence component step slow =
  let
    sourceT = sourceTAt dataSet sequence component step
    quadrature = quadratureAt dataSet sequence component step

    eq171Error =
      Weighted.weightedSliceErrorBound
        quadrature refinement scale slow
  in
  subst
    (λ sourceValue →
      absℝ
        (sourceValue
          -ℝ
         Weighted.weightedGate4MassAt
           quadrature refinement scale slow)
      ≤ℝ
      markedMajorant
        dataSet refinement scale sequence component step slow)
    (sym
      (trans
        (sourceStepIsEquation171Mass
          dataSet scale sequence component step slow)
        (Eq171.equation171DefinesTOperationMass
          sourceT scale slow)))
    eq171Error

asFactorizedDensityApproximation :
  ∀ {trajectory split SlowField Sequence Component Step factorized
      Scale Fine FunctionalValue embedding sequenceLimit} →
  CMP119Equation171WeightedStepApproximation
    {trajectory = trajectory} {split = split}
    {SlowField = SlowField} {Sequence = Sequence}
    {Component = Component} {Step = Step}
    factorized
    {Scale = Scale} {Fine = Fine} {FunctionalValue = FunctionalValue}
    embedding sequenceLimit →
  Approx.CMP119FactorizedDensityApproximation
    SlowField Sequence Component Step
asFactorizedDensityApproximation
  {factorized = factorized} dataSet = record
  { Approx.CMP119FactorizedDensityApproximation.admissibleSequences =
      Factor.admissibleSequences factorized
  ; Approx.CMP119FactorizedDensityApproximation.componentsAt =
      Factor.componentsAt factorized
  ; Approx.CMP119FactorizedDensityApproximation.orderedStepsAt =
      Factor.orderedStepsAt factorized
  ; Approx.CMP119FactorizedDensityApproximation.sourceStep =
      Factor.oneStepValue factorized
  ; Approx.CMP119FactorizedDensityApproximation.approximateStep =
      λ refinement scale sequence component step slow →
        Weighted.weightedGate4MassAt
          (quadratureAt dataSet sequence component step)
          refinement scale slow
  ; Approx.CMP119FactorizedDensityApproximation.ordinaryMajorant =
      ordinaryMajorant dataSet
  ; Approx.CMP119FactorizedDensityApproximation.markedMajorant =
      markedMajorant dataSet
  ; Approx.CMP119FactorizedDensityApproximation.residualFactor =
      Factor.sequenceResidual factorized
  ; Approx.CMP119FactorizedDensityApproximation.residualMajorant =
      residualMajorant dataSet
  ; Approx.CMP119FactorizedDensityApproximation.ordinaryNonnegative =
      ordinaryNonnegative dataSet
  ; Approx.CMP119FactorizedDensityApproximation.markedNonnegative =
      markedMajorantNonnegative dataSet
  ; Approx.CMP119FactorizedDensityApproximation.sourceStepBound =
      sourceStepBound dataSet
  ; Approx.CMP119FactorizedDensityApproximation.approximateStepBound =
      approximateStepBound dataSet
  ; Approx.CMP119FactorizedDensityApproximation.stepDifferenceBound =
      sourceStepToWeightedQuadratureError dataSet
  ; Approx.CMP119FactorizedDensityApproximation.residualMajorantNonnegative =
      residualMajorantNonnegative dataSet
  ; Approx.CMP119FactorizedDensityApproximation.residualBound =
      residualBound dataSet
  }

cmp119Equation171WeightedStepErrorCompilerLevel : ProofLevel
cmp119Equation171WeightedStepErrorCompilerLevel = machineChecked

cmp119Equation171ToFactorizedApproximationCompilerLevel : ProofLevel
cmp119Equation171ToFactorizedApproximationCompilerLevel = machineChecked

-- Remaining one-step analytic/source work:
--  * identify each extracted changed source step with the appropriate Eq.(1.71)
--    source T operation (unchanged steps need their own source realization);
--  * produce a refinement-independent ordinary majorant.
literalCMP119StepIsEquation171OperationLevel : ProofLevel
literalCMP119StepIsEquation171OperationLevel = conditional

literalCMP119StepUniformOrdinaryMajorantLevel : ProofLevel
literalCMP119StepUniformOrdinaryMajorantLevel = conditional
