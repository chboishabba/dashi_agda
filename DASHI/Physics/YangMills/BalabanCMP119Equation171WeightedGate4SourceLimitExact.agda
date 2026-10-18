module DASHI.Physics.YangMills.BalabanCMP119Equation171WeightedGate4SourceLimitExact where

------------------------------------------------------------------------
-- LITERAL CMP119 SOURCE DENSITY -> HAAR-WEIGHTED GATE4 QUADRATURE LIMIT
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
import DASHI.Physics.YangMills.BalabanCMP122Equation171WeightedGate4RefinementLimitExact as WeightedLimit
import DASHI.Physics.YangMills.BalabanClayGate4EmbeddedWeightedQuadratureExact as Weighted

record CMP119Equation171WeightedGate4SourceLimit
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
      WeightedLimit.Equation171WeightedGate4RefinementLimit
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        sourceT embedding sequenceLimit) : Set₁ where
  field
    -- F1b-1: meaning of the selected CMP119 operation/action application.
    sourceApplicationIsEquation171Mass :
      ∀ cutoff slow →
      Weighted.embedQ embedding
        (Assembly.applyOperationAction semantics
          (R219.operationAt family cutoff)
          (R219.effectiveActionAt family cutoff)
          slow)
      ≡
      Eq171.sourceTOperationMass sourceT cutoff slow

open CMP119Equation171WeightedGate4SourceLimit public

sourceApplicationIsWeightedGate4Limit :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional
      semantics sourceT embedding sequenceLimit quadrature}
    (dataSet :
      CMP119Equation171WeightedGate4SourceLimit
        {trajectory = trajectory} {split = split}
        source family
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        semantics sourceT embedding sequenceLimit quadrature)
    cutoff slow →
  Weighted.embedQ embedding
    (Assembly.applyOperationAction semantics
      (R219.operationAt family cutoff)
      (R219.effectiveActionAt family cutoff)
      slow)
  ≡
  Seq.limit sequenceLimit
    (λ refinement →
      WeightedLimit.weightedGate4MassAt
        quadrature refinement cutoff slow)
sourceApplicationIsWeightedGate4Limit
  {quadrature = quadrature} dataSet cutoff slow =
  trans
    (sourceApplicationIsEquation171Mass dataSet cutoff slow)
    (WeightedLimit.equation171SourceMassIsWeightedGate4Limit
      quadrature cutoff slow)

selectedDensityEvaluationIsWeightedGate4Limit :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional
      semantics sourceT embedding sequenceLimit quadrature}
    (dataSet :
      CMP119Equation171WeightedGate4SourceLimit
        {trajectory = trajectory} {split = split}
        source family
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        semantics sourceT embedding sequenceLimit quadrature)
    cutoff slow →
  Weighted.embedQ embedding
    (Assembly.evaluateDensity semantics
      (Beta.densityAt source cutoff)
      slow)
  ≡
  Seq.limit sequenceLimit
    (λ refinement →
      WeightedLimit.weightedGate4MassAt
        quadrature refinement cutoff slow)
selectedDensityEvaluationIsWeightedGate4Limit
  {semantics = semantics} dataSet cutoff slow =
  trans
    (cong
      (Weighted.embedQ _)
      (Assembly.selectedDensityEvaluationIsAssembledWeight
        semantics cutoff slow))
    (sourceApplicationIsWeightedGate4Limit
      dataSet cutoff slow)

cmp119WeightedSourceApplicationLimitCompilerLevel : ProofLevel
cmp119WeightedSourceApplicationLimitCompilerLevel = machineChecked

cmp119WeightedSelectedDensityLimitCompilerLevel : ProofLevel
cmp119WeightedSelectedDensityLimitCompilerLevel = machineChecked

literalCMP119ApplicationEquation171MeaningWeightedLevel : ProofLevel
literalCMP119ApplicationEquation171MeaningWeightedLevel = conditional
