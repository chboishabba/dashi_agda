module DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4RefinementLimitExact where

------------------------------------------------------------------------
-- CMP122 EQ.(1.71) AS THE LIMIT OF GATE4 FINITE CONSTRAINED QUADRATURES
--
-- This is the correct analytic replacement for the false/over-strong target
--
--   literal Haar integral = one selected finite quadrature.
--
-- Each refinement is an exact Gate4 finite constrained fold.  The literal
-- Eq.(1.71) localized compact-Haar integral is identified with the LIMIT of
-- those embedded rational folds.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as AddEmbed
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanCMP122Equation171FiniteConstrainedRealizationExact as Finite

embedQ :
  RingEmbed.RationalRealRingEmbedding → ℚ → ℝ
embedQ embedding =
  AddEmbed.Embed.embed
    (AddEmbed.base (RingEmbed.additive embedding))

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

    finiteRealizationAt : ∀ refinement →
      Finite.CMP122Equation171FiniteConstrainedRealization
        (constructionAt refinement) source embedding

    limit : (Nat → ℝ) → ℝ

    limitCongruent : ∀ left right →
      (∀ refinement → left refinement ≡ right refinement) →
      limit left ≡ limit right

    -- The genuine analytic theorem:
    -- literal Eq.(1.71) localized integration is the product-Haar limit of the
    -- selected finite constrained quadratures, uniformly on this source family.
    equation171IntegralIsQuadratureLimit :
      ∀ cutoff slow →
      Eq171.equation171ConstrainedIntegral source cutoff slow
        (Eq171.equation171ExponentialDensity source cutoff slow)
      ≡
      limit
        (λ refinement →
          Finite.embedQ embedding
            (T.localizedTOperation
              (PhysicalT.canonicalPhysicalTData
                (constructionAt refinement))
              (Finite.scaleAt
                (finiteRealizationAt refinement) cutoff)
              (Finite.selectedAt
                (finiteRealizationAt refinement) cutoff)
              slow
              (T.oneFunctional
                (PhysicalT.canonicalPhysicalTData
                  (constructionAt refinement)))))

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
  Finite.embedQ _
    (T.localizedTOperation
      (PhysicalT.canonicalPhysicalTData
        (constructionAt dataSet refinement))
      (Finite.scaleAt
        (finiteRealizationAt dataSet refinement) cutoff)
      (Finite.selectedAt
        (finiteRealizationAt dataSet refinement) cutoff)
      slow
      (T.oneFunctional
        (PhysicalT.canonicalPhysicalTData
          (constructionAt dataSet refinement))))

equation171IntegralIsGate4QuadratureLimit :
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
equation171IntegralIsGate4QuadratureLimit dataSet cutoff slow =
  equation171IntegralIsQuadratureLimit dataSet cutoff slow

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
    (equation171IntegralIsGate4QuadratureLimit dataSet cutoff slow)

equation171Gate4RefinementCompilerLevel : ProofLevel
equation171Gate4RefinementCompilerLevel = machineChecked

equation171SourceMassQuadratureLimitCompilerLevel : ProofLevel
equation171SourceMassQuadratureLimitCompilerLevel = machineChecked

-- This is the real hard analytic theorem.  It must identify the chosen
-- refinement family with product compact-Haar disintegration for Eq.(1.71),
-- including domination/uniformity in cutoff, component and slow field.
literalEquation171ProductHaarQuadratureLimitLevel : ProofLevel
literalEquation171ProductHaarQuadratureLimitLevel = conditional
