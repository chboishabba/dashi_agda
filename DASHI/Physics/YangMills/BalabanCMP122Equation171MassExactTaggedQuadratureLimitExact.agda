module DASHI.Physics.YangMills.BalabanCMP122Equation171MassExactTaggedQuadratureLimitExact where

------------------------------------------------------------------------
-- CMP122 EQ.(1.71) VIA MASS-EXACT TAGGED PRODUCT-HAAR QUADRATURE
--
-- Exact Haar cell masses kill the discrepancy term identically.
-- The only asymptotic error is the common cell-oscillation modulus.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4QuadratureSliceExact as Slice
import DASHI.Physics.YangMills.BalabanCompactHaarMassExactTaggedPartitionExact as Tagged
import DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact as Error
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCMP122Equation171QuantitativeQuadratureLimitExact as Quant
import DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4RefinementLimitExact as Limit

record CMP122Equation171MassExactTaggedQuadratureLimit
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

    taggedPartitionAt : ∀ refinement cutoff slow →
      Tagged.MassExactTaggedPartition
        (Cell refinement cutoff slow)

    taggedSourceIsEquation171Integral :
      ∀ refinement cutoff slow →
      Tagged.taggedSourceIntegral
        (taggedPartitionAt refinement cutoff slow)
      ≡
      Eq171.equation171ConstrainedIntegral source cutoff slow
        (Eq171.equation171ExponentialDensity source cutoff slow)

    taggedQuadratureIsSliceFold :
      ∀ refinement cutoff slow →
      Tagged.taggedQuadratureSum
        (taggedPartitionAt refinement cutoff slow)
      ≡
      Slice.sourceFiniteFold
        (sliceAt refinement) cutoff slow

    oscillationModulusVanishes :
      ∀ cutoff slow →
      Seq.Vanishes sequenceLimit
        (λ refinement →
          Tagged.modulus
            (taggedPartitionAt refinement cutoff slow))

open CMP122Equation171MassExactTaggedQuadratureLimit public

errorBudgetIsOscillationModulus :
  ∀ {Scale Fine SlowField Component Functional source embedding sequenceLimit}
    (dataSet :
      CMP122Equation171MassExactTaggedQuadratureLimit
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        source embedding sequenceLimit)
    refinement cutoff slow →
  Error.totalErrorBudget
    (Tagged.asFiniteQuadratureCellError
      (taggedPartitionAt dataSet refinement cutoff slow))
  ≡
  Tagged.modulus
    (taggedPartitionAt dataSet refinement cutoff slow)
errorBudgetIsOscillationModulus dataSet refinement cutoff slow =
  Tagged.totalBudgetIsModulus
    (taggedPartitionAt dataSet refinement cutoff slow)

errorBudgetVanishes :
  ∀ {Scale Fine SlowField Component Functional source embedding sequenceLimit}
    (dataSet :
      CMP122Equation171MassExactTaggedQuadratureLimit
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        source embedding sequenceLimit)
    cutoff slow →
  Seq.Vanishes sequenceLimit
    (λ refinement →
      Error.totalErrorBudget
        (Tagged.asFiniteQuadratureCellError
          (taggedPartitionAt dataSet refinement cutoff slow)))
errorBudgetVanishes
  {sequenceLimit = sequenceLimit} dataSet cutoff slow =
  Seq.vanishesCongruent sequenceLimit
    (λ refinement →
      Tagged.modulus
        (taggedPartitionAt dataSet refinement cutoff slow))
    (λ refinement →
      Error.totalErrorBudget
        (Tagged.asFiniteQuadratureCellError
          (taggedPartitionAt dataSet refinement cutoff slow)))
    (λ refinement →
      Relation.Binary.PropositionalEquality.sym
        (errorBudgetIsOscillationModulus
          dataSet refinement cutoff slow))
    (oscillationModulusVanishes dataSet cutoff slow)
  where
  import Relation.Binary.PropositionalEquality

asQuantitativeQuadratureLimit :
  ∀ {Scale Fine SlowField Component Functional
      source embedding sequenceLimit} →
  CMP122Equation171MassExactTaggedQuadratureLimit
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    source embedding sequenceLimit →
  Quant.CMP122Equation171QuantitativeQuadratureLimit
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    source embedding sequenceLimit
asQuantitativeQuadratureLimit dataSet = record
  { Quant.CMP122Equation171QuantitativeQuadratureLimit.constructionAt =
      constructionAt dataSet
  ; Quant.CMP122Equation171QuantitativeQuadratureLimit.sliceAt =
      sliceAt dataSet
  ; Quant.CMP122Equation171QuantitativeQuadratureLimit.Cell =
      Cell dataSet
  ; Quant.CMP122Equation171QuantitativeQuadratureLimit.cellErrorAt =
      λ refinement cutoff slow →
        Tagged.asFiniteQuadratureCellError
          (taggedPartitionAt dataSet refinement cutoff slow)
  ; Quant.CMP122Equation171QuantitativeQuadratureLimit.sourceCellSumIsEquation171Integral =
      taggedSourceIsEquation171Integral dataSet
  ; Quant.CMP122Equation171QuantitativeQuadratureLimit.quadratureCellSumIsSliceFold =
      taggedQuadratureIsSliceFold dataSet
  ; Quant.CMP122Equation171QuantitativeQuadratureLimit.errorBudgetVanishes =
      errorBudgetVanishes dataSet
  }

compileEquation171Gate4RefinementLimit :
  ∀ {Scale Fine SlowField Component Functional
      source embedding sequenceLimit} →
  CMP122Equation171MassExactTaggedQuadratureLimit
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    source embedding sequenceLimit →
  Limit.Equation171Gate4RefinementLimit
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    source embedding
compileEquation171Gate4RefinementLimit dataSet =
  Quant.compileEquation171Gate4RefinementLimit
    (asQuantitativeQuadratureLimit dataSet)

massExactEquation171QuadratureCompilerLevel : ProofLevel
massExactEquation171QuadratureCompilerLevel = machineChecked

massExactEquation171DiscrepancyEliminationLevel : ProofLevel
massExactEquation171DiscrepancyEliminationLevel = machineChecked

literalEquation171MassExactTaggedPartitionLevel : ProofLevel
literalEquation171MassExactTaggedPartitionLevel = conditional

literalEquation171OscillationModulusVanishesLevel : ProofLevel
literalEquation171OscillationModulusVanishesLevel = conditional
