module DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4RefinementLimitExact where

------------------------------------------------------------------------
-- CMP122 EQ.(1.71) AS THE LIMIT OF GATE4 FINITE CONSTRAINED QUADRATURES
--
-- Each refinement slice pays only G1/G2/G3 representation obligations.
-- The literal Eq.(1.71) localized compact-Haar integral is identified with the
-- LIMIT of those exact finite slices.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4QuadratureSliceExact as Slice

record Equation171Gate4RefinementLimit
    {Scale Fine SlowField Component Functional : Set}
    (source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField)
    (embedding :
      RingEmbed.RationalRealRingEmbedding) : Set₂ where
  field
    constructionAt :
      Nat →
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional

    sliceAt : ∀ refinement →
      Slice.Equation171Gate4QuadratureSlice
        (constructionAt refinement) source embedding

    limit : (Nat → ℝ) → ℝ

    limitCongruent : ∀ left right →
      (∀ refinement → left refinement ≡ right refinement) →
      limit left ≡ limit right

    -- The actual hard analytic theorem:
    -- product-Haar/localized Eq.(1.71) integration is the limit of the chosen
    -- equidistributed finite Gate4 quadratures.
    equation171IntegralIsQuadratureLimit :
      ∀ cutoff slow →
      Eq171.equation171ConstrainedIntegral source cutoff slow
        (Eq171.equation171ExponentialDensity source cutoff slow)
      ≡
      limit
        (λ refinement →
          Slice.sourceFiniteFold
            (sliceAt refinement) cutoff slow)

open Equation171Gate4RefinementLimit public

embeddedGate4MassAt :
  ∀ {Scale Fine SlowField Component Functional}
    {source : Eq171.CMP122Equation171TOperationSemantics Fine SlowField}
    {embedding : RingEmbed.RationalRealRingEmbedding} →
  Equation171Gate4RefinementLimit
    {Scale = Scale} {Component = Component} {Functional = Functional}
    source embedding →
  Nat → Nat → SlowField → ℝ
embeddedGate4MassAt dataSet refinement cutoff slow =
  Slice.embeddedGate4Mass
    (sliceAt dataSet refinement) cutoff slow

equation171IntegralIsEmbeddedGate4QuadratureLimit :
  ∀ {Scale Fine SlowField Component Functional}
    {source : Eq171.CMP122Equation171TOperationSemantics Fine SlowField}
    {embedding : RingEmbed.RationalRealRingEmbedding}
    (dataSet :
      Equation171Gate4RefinementLimit
        {Scale = Scale} {Component = Component} {Functional = Functional}
        source embedding)
    cutoff slow →
  Eq171.equation171ConstrainedIntegral source cutoff slow
    (Eq171.equation171ExponentialDensity source cutoff slow)
  ≡
  limit dataSet
    (λ refinement →
      embeddedGate4MassAt dataSet refinement cutoff slow)
equation171IntegralIsEmbeddedGate4QuadratureLimit dataSet cutoff slow =
  trans
    (equation171IntegralIsQuadratureLimit dataSet cutoff slow)
    (limitCongruent dataSet
      (λ refinement →
        Slice.sourceFiniteFold
          (sliceAt dataSet refinement) cutoff slow)
      (λ refinement →
        embeddedGate4MassAt dataSet refinement cutoff slow)
      (λ refinement →
        Slice.sourceFiniteFoldIsEmbeddedGate4Mass
          (sliceAt dataSet refinement) cutoff slow))

equation171SourceMassIsGate4QuadratureLimit :
  ∀ {Scale Fine SlowField Component Functional}
    {source : Eq171.CMP122Equation171TOperationSemantics Fine SlowField}
    {embedding : RingEmbed.RationalRealRingEmbedding}
    (dataSet :
      Equation171Gate4RefinementLimit
        {Scale = Scale} {Component = Component} {Functional = Functional}
        source embedding)
    cutoff slow →
  Eq171.sourceTOperationMass source cutoff slow
  ≡
  limit dataSet
    (λ refinement →
      embeddedGate4MassAt dataSet refinement cutoff slow)
equation171SourceMassIsGate4QuadratureLimit dataSet cutoff slow =
  trans
    (Eq171.equation171DefinesTOperationMass _ cutoff slow)
    (equation171IntegralIsEmbeddedGate4QuadratureLimit
      dataSet cutoff slow)

equation171Gate4RefinementSliceCompilerLevel : ProofLevel
equation171Gate4RefinementSliceCompilerLevel = machineChecked

equation171SourceMassQuadratureLimitCompilerLevel : ProofLevel
equation171SourceMassQuadratureLimitCompilerLevel = machineChecked

-- The one remaining analytic theorem at this layer.  It must prove actual
-- product-Haar quadrature convergence with enough domination/uniformity for the
-- selected Eq.(1.71) source density.
literalEquation171ProductHaarQuadratureLimitLevel : ProofLevel
literalEquation171ProductHaarQuadratureLimitLevel = conditional
