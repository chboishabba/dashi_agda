module DASHI.Physics.YangMills.BalabanCMP119Equation171Gate4RefinementSourceLimitExact where

------------------------------------------------------------------------
-- CMP119 SOURCE APPLICATION / DENSITY -> LIMIT OF GATE4 QUADRATURE MASSES
--
-- This is the correct same-object statement after the Haar audit:
--
--   embedded applyOperationAction(T_k,A_k)
--     = Eq.(1.71) source T-mass
--     = lim_n embedded Gate4Mass_n.
--
-- Composing with the source-fixed assembly semantics also gives the same limit
-- for evaluation of the selected literal beta-driven density.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119FiniteDensityAssemblySemanticsExact as Assembly
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4RefinementLimitExact as Limit
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4QuadratureSliceExact as Slice

record CMP119Equation171Gate4RefinementSourceLimit
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
    (quadrature :
      Limit.Equation171Gate4RefinementLimit
        {Scale = Scale} {Component = Component} {Functional = Functional}
        sourceT embedding) : Set₁ where
  field
    sourceApplicationIsEquation171Mass :
      ∀ cutoff slow →
      Slice.embedQ embedding
        (Assembly.applyOperationAction semantics
          (R219.operationAt family cutoff)
          (R219.effectiveActionAt family cutoff)
          slow)
      ≡
      Eq171.sourceTOperationMass sourceT cutoff slow

open CMP119Equation171Gate4RefinementSourceLimit public

sourceApplicationIsGate4QuadratureLimit :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional
      semantics sourceT embedding quadrature}
    (dataSet :
      CMP119Equation171Gate4RefinementSourceLimit
        {trajectory = trajectory} {split = split}
        source family
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        semantics sourceT embedding quadrature)
    cutoff slow →
  Slice.embedQ embedding
    (Assembly.applyOperationAction semantics
      (R219.operationAt family cutoff)
      (R219.effectiveActionAt family cutoff)
      slow)
  ≡
  Limit.limit quadrature
    (λ refinement →
      Limit.embeddedGate4MassAt
        quadrature refinement cutoff slow)
sourceApplicationIsGate4QuadratureLimit
  {quadrature = quadrature} dataSet cutoff slow =
  trans
    (sourceApplicationIsEquation171Mass dataSet cutoff slow)
    (Limit.equation171SourceMassIsGate4QuadratureLimit
      quadrature cutoff slow)

selectedDensityEvaluationIsGate4QuadratureLimit :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional
      semantics sourceT embedding quadrature}
    (dataSet :
      CMP119Equation171Gate4RefinementSourceLimit
        {trajectory = trajectory} {split = split}
        source family
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        semantics sourceT embedding quadrature)
    cutoff slow →
  Slice.embedQ embedding
    (Assembly.evaluateDensity semantics
      (Beta.densityAt source cutoff)
      slow)
  ≡
  Limit.limit quadrature
    (λ refinement →
      Limit.embeddedGate4MassAt
        quadrature refinement cutoff slow)
selectedDensityEvaluationIsGate4QuadratureLimit
  {semantics = semantics} dataSet cutoff slow =
  trans
    (cong
      (Slice.embedQ _)
      (Assembly.selectedDensityEvaluationIsAssembledWeight
        semantics cutoff slow))
    (sourceApplicationIsGate4QuadratureLimit dataSet cutoff slow)

cmp119SourceApplicationQuadratureLimitCompilerLevel : ProofLevel
cmp119SourceApplicationQuadratureLimitCompilerLevel = machineChecked

cmp119SelectedDensityQuadratureLimitCompilerLevel : ProofLevel
cmp119SelectedDensityQuadratureLimitCompilerLevel = machineChecked

literalCMP119ApplicationIsEquation171MassLimitLevel : ProofLevel
literalCMP119ApplicationIsEquation171MassLimitLevel = conditional
