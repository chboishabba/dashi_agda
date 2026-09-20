module DASHI.Physics.YangMills.BalabanCMP119Equation171Gate4ContributionSourceLimitExact where

------------------------------------------------------------------------
-- CMP119 SOURCE DENSITY = LIMIT OF EXECUTABLE GATE4 CONTRIBUTIONS
--
-- This is the corrected canonical source theorem:
--
--   evaluate densityAt_k
--     -> selected source application(T_k,A_k)
--     -> Eq.(1.71) localized source mass
--     -> limit of embedded executable Gate4 finite sums.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119FiniteDensityAssemblySemanticsExact as Assembly
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4ContributionRefinementLimitExact as Limit
import DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4ContributionQuadratureExact as Quad

record CMP119Equation171Gate4ContributionSourceLimit
    {trajectory split}
    (source :
      Beta.BetaDrivenCompleteDensityInputs
        {trajectory = trajectory} {split = split})
    (family : R219.BetaDrivenCMP119ResidualFamily source)
    {Scale Fine SlowField Component Functional : Set}
    (semantics :
      Assembly.CMP119FiniteDensityAssemblySemantics
        source family SlowField)
    (sourceT :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField)
    (embedding :
      RingEmbed.RationalRealRingEmbedding)
    (sequenceLimit :
      Seq.RealSequenceLimitByVanishingError)
    (quadrature :
      Limit.Equation171Gate4ContributionRefinementLimit
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        sourceT embedding sequenceLimit) : Set₁ where
  field
    sourceApplicationIsEquation171Mass :
      ∀ cutoff slow →
      Quad.embedQ embedding
        (Assembly.applyOperationAction semantics
          (R219.operationAt family cutoff)
          (R219.effectiveActionAt family cutoff)
          slow)
      ≡
      Eq171.sourceTOperationMass sourceT cutoff slow

open CMP119Equation171Gate4ContributionSourceLimit public

sourceApplicationIsExecutableGate4Limit :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional
      semantics sourceT embedding sequenceLimit quadrature}
    (dataSet :
      CMP119Equation171Gate4ContributionSourceLimit
        {trajectory = trajectory} {split = split}
        source family
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        semantics sourceT embedding sequenceLimit quadrature)
    cutoff slow →
  Quad.embedQ embedding
    (Assembly.applyOperationAction semantics
      (R219.operationAt family cutoff)
      (R219.effectiveActionAt family cutoff)
      slow)
  ≡
  Seq.limit sequenceLimit
    (λ refinement →
      Limit.embeddedGate4MassAt
        quadrature refinement cutoff slow)
sourceApplicationIsExecutableGate4Limit
  {quadrature = quadrature} dataSet cutoff slow =
  trans
    (sourceApplicationIsEquation171Mass dataSet cutoff slow)
    (Limit.equation171SourceMassIsExecutableGate4Limit
      quadrature cutoff slow)

selectedDensityEvaluationIsExecutableGate4Limit :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional
      semantics sourceT embedding sequenceLimit quadrature}
    (dataSet :
      CMP119Equation171Gate4ContributionSourceLimit
        {trajectory = trajectory} {split = split}
        source family
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        semantics sourceT embedding sequenceLimit quadrature)
    cutoff slow →
  Quad.embedQ embedding
    (Assembly.evaluateDensity semantics
      (Beta.densityAt source cutoff)
      slow)
  ≡
  Seq.limit sequenceLimit
    (λ refinement →
      Limit.embeddedGate4MassAt
        quadrature refinement cutoff slow)
selectedDensityEvaluationIsExecutableGate4Limit
  {semantics = semantics} dataSet cutoff slow =
  trans
    (cong
      (Quad.embedQ _)
      (Assembly.selectedDensityEvaluationIsAssembledWeight
        semantics cutoff slow))
    (sourceApplicationIsExecutableGate4Limit
      dataSet cutoff slow)

cmp119ExecutableGate4SourceLimitCompilerLevel : ProofLevel
cmp119ExecutableGate4SourceLimitCompilerLevel = machineChecked

cmp119SelectedDensityExecutableLimitCompilerLevel : ProofLevel
cmp119SelectedDensityExecutableLimitCompilerLevel = machineChecked

literalCMP119ApplicationEquation171MassLevel : ProofLevel
literalCMP119ApplicationEquation171MassLevel = conditional
