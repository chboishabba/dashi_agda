module DASHI.Physics.YangMills.BalabanCMP122Equation171QuantitativeQuadratureLimitExact where

------------------------------------------------------------------------
-- QUANTITATIVE PRODUCT-HAAR QUADRATURE COMPILER FOR CMP122 EQ.(1.71)
--
-- Every finite cell decomposition is indexed by
--
--   refinement x cutoff x slow field.
--
-- This is essential: Eq.(1.71)'s selected domain and density depend on the
-- physical cutoff/background.  The compiler proves convergence pointwise on
-- that exact source family.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; absℝ; _-ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4QuadratureSliceExact as Slice
import DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4RefinementLimitExact as Limit
import DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact as Error
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

record CMP122Equation171QuantitativeQuadratureLimit
    {Scale Fine SlowField Component Functional : Set}
    (source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField)
    (embedding :
      RingEmbed.RationalRealRingEmbedding)
    (sequenceLimit :
      Seq.RealSequenceLimitByVanishingError) : Set₂ where
  field
    constructionAt :
      Nat →
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional

    sliceAt : ∀ refinement →
      Slice.Equation171Gate4QuadratureSlice
        (constructionAt refinement) source embedding

    Cell : Nat → Nat → SlowField → Set

    cellErrorAt : ∀ refinement cutoff slow →
      Error.FiniteQuadratureCellError
        (Cell refinement cutoff slow)

    sourceCellSumIsEquation171Integral :
      ∀ refinement cutoff slow →
      Error.sourceIntegral
        (cellErrorAt refinement cutoff slow)
      ≡
      Eq171.equation171ConstrainedIntegral source cutoff slow
        (Eq171.equation171ExponentialDensity source cutoff slow)

    quadratureCellSumIsSliceFold :
      ∀ refinement cutoff slow →
      Error.quadratureSum
        (cellErrorAt refinement cutoff slow)
      ≡
      Slice.sourceFiniteFold
        (sliceAt refinement) cutoff slow

    errorBudgetVanishes :
      ∀ cutoff slow →
      Seq.Vanishes sequenceLimit
        (λ refinement →
          Error.totalErrorBudget
            (cellErrorAt refinement cutoff slow))

open CMP122Equation171QuantitativeQuadratureLimit public

sliceFoldErrorBound :
  ∀ {Scale Fine SlowField Component Functional}
    {source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField}
    {embedding : RingEmbed.RationalRealRingEmbedding}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (dataSet :
      CMP122Equation171QuantitativeQuadratureLimit
        {Scale = Scale} {Component = Component} {Functional = Functional}
        source embedding sequenceLimit)
    refinement cutoff slow →
  absℝ
    (Eq171.equation171ConstrainedIntegral source cutoff slow
      (Eq171.equation171ExponentialDensity source cutoff slow)
      -ℝ
      Slice.sourceFiniteFold
        (sliceAt dataSet refinement) cutoff slow)
  ≤ℝ
  Error.totalErrorBudget
    (cellErrorAt dataSet refinement cutoff slow)
sliceFoldErrorBound dataSet refinement cutoff slow =
  subst
    (λ sourceValue →
      absℝ
        (sourceValue
          -ℝ
          Slice.sourceFiniteFold
            (sliceAt dataSet refinement) cutoff slow)
      ≤ℝ
      Error.totalErrorBudget
        (cellErrorAt dataSet refinement cutoff slow))
    (sourceCellSumIsEquation171Integral
      dataSet refinement cutoff slow)
    (subst
      (λ quadratureValue →
        absℝ
          (Error.sourceIntegral
            (cellErrorAt dataSet refinement cutoff slow)
            -ℝ quadratureValue)
        ≤ℝ
        Error.totalErrorBudget
          (cellErrorAt dataSet refinement cutoff slow))
      (quadratureCellSumIsSliceFold
        dataSet refinement cutoff slow)
      (Error.finiteQuadratureErrorBound
        (cellErrorAt dataSet refinement cutoff slow)))

equation171IntegralIsFiniteSliceLimit :
  ∀ {Scale Fine SlowField Component Functional}
    {source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField}
    {embedding : RingEmbed.RationalRealRingEmbedding}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (dataSet :
      CMP122Equation171QuantitativeQuadratureLimit
        {Scale = Scale} {Component = Component} {Functional = Functional}
        source embedding sequenceLimit)
    cutoff slow →
  Eq171.equation171ConstrainedIntegral source cutoff slow
    (Eq171.equation171ExponentialDensity source cutoff slow)
  ≡
  Seq.limit sequenceLimit
    (λ refinement →
      Slice.sourceFiniteFold
        (sliceAt dataSet refinement) cutoff slow)
equation171IntegralIsFiniteSliceLimit
  {sequenceLimit = sequenceLimit} dataSet cutoff slow =
  sym
    (Seq.limitFromVanishingError sequenceLimit
      (λ refinement →
        Slice.sourceFiniteFold
          (sliceAt dataSet refinement) cutoff slow)
      (Eq171.equation171ConstrainedIntegral source cutoff slow
        (Eq171.equation171ExponentialDensity source cutoff slow))
      (λ refinement →
        Error.totalErrorBudget
          (cellErrorAt dataSet refinement cutoff slow))
      (λ refinement →
        sliceFoldErrorBound dataSet refinement cutoff slow)
      (errorBudgetVanishes dataSet cutoff slow))

compileEquation171Gate4RefinementLimit :
  ∀ {Scale Fine SlowField Component Functional}
    {source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField}
    {embedding : RingEmbed.RationalRealRingEmbedding}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError} →
  CMP122Equation171QuantitativeQuadratureLimit
    {Scale = Scale} {Component = Component} {Functional = Functional}
    source embedding sequenceLimit →
  Limit.Equation171Gate4RefinementLimit
    {Scale = Scale} {Component = Component} {Functional = Functional}
    source embedding
compileEquation171Gate4RefinementLimit
  {sequenceLimit = sequenceLimit} dataSet = record
  { Limit.Equation171Gate4RefinementLimit.constructionAt =
      constructionAt dataSet
  ; Limit.Equation171Gate4RefinementLimit.sliceAt =
      sliceAt dataSet
  ; Limit.Equation171Gate4RefinementLimit.limit =
      Seq.limit sequenceLimit
  ; Limit.Equation171Gate4RefinementLimit.limitCongruent =
      Seq.limitCongruent sequenceLimit
  ; Limit.Equation171Gate4RefinementLimit.equation171IntegralIsQuadratureLimit =
      equation171IntegralIsFiniteSliceLimit dataSet
  }

equation171QuantitativeQuadratureCompilerLevel : ProofLevel
equation171QuantitativeQuadratureCompilerLevel = machineChecked

equation171QuantitativeRefinementLimitCompilerLevel : ProofLevel
equation171QuantitativeRefinementLimitCompilerLevel = machineChecked

literalEquation171CellDecompositionLevel : ProofLevel
literalEquation171CellDecompositionLevel = conditional

literalEquation171OscillationBudgetVanishesLevel : ProofLevel
literalEquation171OscillationBudgetVanishesLevel = conditional

literalEquation171DiscrepancyBudgetVanishesLevel : ProofLevel
literalEquation171DiscrepancyBudgetVanishesLevel = conditional
