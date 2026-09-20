module DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4ContributionRefinementLimitExact where

------------------------------------------------------------------------
-- CMP122 EQ.(1.71) = LIMIT OF EXECUTABLE GATE4 CONTRIBUTION QUADRATURES
--
-- No exact pointwise source-density = rational-activity claim is used.
-- Convergence follows from:
--
--   source-cell oscillation -> 0
--   weighted executable-contribution approximation -> 0.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4ContributionQuadratureExact as Quad
import DASHI.Physics.YangMills.BalabanCompactHaarMassExactContributionApproximationExact as Approx
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

record Equation171Gate4ContributionRefinementLimit
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

    quadratureAt : ∀ refinement →
      Quad.Equation171Gate4ContributionQuadrature
        (constructionAt refinement) source embedding

    combinedModulusVanishes :
      ∀ cutoff slow →
      Seq.Vanishes sequenceLimit
        (λ refinement →
          Approx.combinedModulus
            (Quad.asContributionApproximation
              (quadratureAt refinement)
              cutoff slow))

open Equation171Gate4ContributionRefinementLimit public

embeddedGate4MassAt :
  ∀ {Scale Fine SlowField Component Functional source embedding sequenceLimit}
    (dataSet :
      Equation171Gate4ContributionRefinementLimit
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        source embedding sequenceLimit) →
  Nat → Nat → SlowField → ℝ
embeddedGate4MassAt
  {embedding = embedding}
  dataSet refinement cutoff slow =
  Quad.embedQ embedding
    (T.localizedTOperation
      (PhysicalT.canonicalPhysicalTData
        (constructionAt dataSet refinement))
      (Quad.scaleAt (quadratureAt dataSet refinement) cutoff)
      (Quad.selectedAt (quadratureAt dataSet refinement) cutoff)
      slow
      (T.oneFunctional
        (PhysicalT.canonicalPhysicalTData
          (constructionAt dataSet refinement))))

equation171IntegralIsExecutableGate4Limit :
  ∀ {Scale Fine SlowField Component Functional source embedding sequenceLimit}
    (dataSet :
      Equation171Gate4ContributionRefinementLimit
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        source embedding sequenceLimit)
    cutoff slow →
  Eq171.equation171ConstrainedIntegral source cutoff slow
    (Eq171.equation171ExponentialDensity source cutoff slow)
  ≡
  Seq.limit sequenceLimit
    (λ refinement →
      embeddedGate4MassAt dataSet refinement cutoff slow)
equation171IntegralIsExecutableGate4Limit
  {source = source} {sequenceLimit = sequenceLimit}
  dataSet cutoff slow =
  sym
    (Seq.limitFromVanishingError sequenceLimit
      (λ refinement →
        embeddedGate4MassAt dataSet refinement cutoff slow)
      (Eq171.equation171ConstrainedIntegral source cutoff slow
        (Eq171.equation171ExponentialDensity source cutoff slow))
      (λ refinement →
        Approx.combinedModulus
          (Quad.asContributionApproximation
            (quadratureAt dataSet refinement)
            cutoff slow))
      (λ refinement →
        Quad.equation171ToEmbeddedGate4ErrorBound
          (quadratureAt dataSet refinement)
          cutoff slow)
      (combinedModulusVanishes dataSet cutoff slow))

equation171SourceMassIsExecutableGate4Limit :
  ∀ {Scale Fine SlowField Component Functional source embedding sequenceLimit}
    (dataSet :
      Equation171Gate4ContributionRefinementLimit
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        source embedding sequenceLimit)
    cutoff slow →
  Eq171.sourceTOperationMass source cutoff slow
  ≡
  Seq.limit sequenceLimit
    (λ refinement →
      embeddedGate4MassAt dataSet refinement cutoff slow)
equation171SourceMassIsExecutableGate4Limit
  {source = source} dataSet cutoff slow =
  trans
    (Eq171.equation171DefinesTOperationMass source cutoff slow)
    (equation171IntegralIsExecutableGate4Limit
      dataSet cutoff slow)

equation171ContributionRefinementCompilerLevel : ProofLevel
equation171ContributionRefinementCompilerLevel = machineChecked

equation171ExecutableGate4LimitCompilerLevel : ProofLevel
equation171ExecutableGate4LimitCompilerLevel = machineChecked

-- The exact hard content is now reduced to the two explicit moduli.
literalEquation171OscillationVanishesLevel : ProofLevel
literalEquation171OscillationVanishesLevel = conditional

literalGate4ContributionApproximationVanishesLevel : ProofLevel
literalGate4ContributionApproximationVanishesLevel = conditional
