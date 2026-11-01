module DASHI.Physics.YangMills.BalabanCMP122Equation171WeightedGate4RefinementLimitExact where

------------------------------------------------------------------------
-- LITERAL EQ.(1.71) = LIMIT OF HAAR-WEIGHTED GATE4 QUADRATURES
--
-- The legacy rational Gate4 T-operation is intentionally absent here.
-- Every finite refinement is the real tagged sum
--
--   sum_C mu_Haar(C) * embed(Gate4.oneIntegrand(tag C)).
--
-- Mass discrepancy is zero by construction.  The only asymptotic payment is
-- the common tagged-cell oscillation modulus.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; absℝ; _-ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanCMP122Equation171WeightedGate4QuadratureSliceExact as Slice
import DASHI.Physics.YangMills.BalabanCompactHaarMassExactTaggedPartitionExact as Tagged
import DASHI.Physics.YangMills.BalabanClayGate4EmbeddedWeightedQuadratureExact as Weighted
import DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact as Error
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

record Equation171WeightedGate4RefinementLimit
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
      Slice.Equation171WeightedGate4QuadratureSlice
        (constructionAt refinement) source embedding

    oscillationModulusVanishes :
      ∀ cutoff slow →
      Seq.Vanishes sequenceLimit
        (λ refinement →
          Tagged.modulus
            (Slice.taggedAt
              (sliceAt refinement) cutoff slow))

open Equation171WeightedGate4RefinementLimit public

weightedGate4MassAt :
  ∀ {Scale Fine SlowField Component Functional}
    {source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField}
    {embedding : RingEmbed.RationalRealRingEmbedding}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError} →
  Equation171WeightedGate4RefinementLimit
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    source embedding sequenceLimit →
  Nat → Nat → SlowField → ℝ
weightedGate4MassAt dataSet refinement cutoff slow =
  Weighted.weightedGate4Quadrature
    (Slice.weighted (sliceAt dataSet refinement))
    (Slice.scaleAt (sliceAt dataSet refinement) cutoff)
    (Slice.selectedAt (sliceAt dataSet refinement) cutoff)
    slow

weightedSliceErrorBound :
  ∀ {Scale Fine SlowField Component Functional}
    {source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField}
    {embedding : RingEmbed.RationalRealRingEmbedding}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (dataSet :
      Equation171WeightedGate4RefinementLimit
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        source embedding sequenceLimit)
    refinement cutoff slow →
  absℝ
    (Eq171.equation171ConstrainedIntegral source cutoff slow
      (Eq171.equation171ExponentialDensity source cutoff slow)
      -ℝ
      weightedGate4MassAt dataSet refinement cutoff slow)
  ≤ℝ
  Tagged.modulus
    (Slice.taggedAt
      (sliceAt dataSet refinement) cutoff slow)
weightedSliceErrorBound dataSet refinement cutoff slow =
  let
    slice = sliceAt dataSet refinement
    tagged = Slice.taggedAt slice cutoff slow
  in
  subst
    (λ sourceValue →
      absℝ
        (sourceValue
          -ℝ weightedGate4MassAt
            dataSet refinement cutoff slow)
      ≤ℝ Tagged.modulus tagged)
    (Slice.sourcePartitionIsEquation171Integral
      slice cutoff slow)
    (subst
      (λ quadratureValue →
        absℝ
          (Tagged.taggedSourceIntegral tagged
            -ℝ quadratureValue)
        ≤ℝ Tagged.modulus tagged)
      (Slice.taggedQuadratureIsWeightedGate4
        slice cutoff slow)
      (Tagged.massExactTaggedPartitionError tagged))

equation171IntegralIsWeightedGate4Limit :
  ∀ {Scale Fine SlowField Component Functional}
    {source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField}
    {embedding : RingEmbed.RationalRealRingEmbedding}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (dataSet :
      Equation171WeightedGate4RefinementLimit
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        source embedding sequenceLimit)
    cutoff slow →
  Eq171.equation171ConstrainedIntegral source cutoff slow
    (Eq171.equation171ExponentialDensity source cutoff slow)
  ≡
  Seq.limit sequenceLimit
    (λ refinement →
      weightedGate4MassAt dataSet refinement cutoff slow)
equation171IntegralIsWeightedGate4Limit
  {sequenceLimit = sequenceLimit} dataSet cutoff slow =
  sym
    (Seq.limitFromVanishingError sequenceLimit
      (λ refinement →
        weightedGate4MassAt dataSet refinement cutoff slow)
      (Eq171.equation171ConstrainedIntegral source cutoff slow
        (Eq171.equation171ExponentialDensity source cutoff slow))
      (λ refinement →
        Tagged.modulus
          (Slice.taggedAt
            (sliceAt dataSet refinement) cutoff slow))
      (λ refinement →
        weightedSliceErrorBound
          dataSet refinement cutoff slow)
      (oscillationModulusVanishes dataSet cutoff slow))

equation171SourceMassIsWeightedGate4Limit :
  ∀ {Scale Fine SlowField Component Functional}
    {source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField}
    {embedding : RingEmbed.RationalRealRingEmbedding}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (dataSet :
      Equation171WeightedGate4RefinementLimit
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        source embedding sequenceLimit)
    cutoff slow →
  Eq171.sourceTOperationMass source cutoff slow
  ≡
  Seq.limit sequenceLimit
    (λ refinement →
      weightedGate4MassAt dataSet refinement cutoff slow)
equation171SourceMassIsWeightedGate4Limit dataSet cutoff slow =
  trans
    (Eq171.equation171DefinesTOperationMass _ cutoff slow)
    (equation171IntegralIsWeightedGate4Limit dataSet cutoff slow)

weightedEquation171RefinementLimitCompilerLevel : ProofLevel
weightedEquation171RefinementLimitCompilerLevel = machineChecked

weightedEquation171SourceMassLimitCompilerLevel : ProofLevel
weightedEquation171SourceMassLimitCompilerLevel = machineChecked

-- Mass discrepancy is no longer a leaf.  Remaining analysis is precisely the
-- source partition/tag construction and the vanishing oscillation modulus.
literalEquation171WeightedPartitionFamilyLevel : ProofLevel
literalEquation171WeightedPartitionFamilyLevel = conditional

literalEquation171WeightedOscillationVanishesLevel : ProofLevel
literalEquation171WeightedOscillationVanishesLevel = conditional
