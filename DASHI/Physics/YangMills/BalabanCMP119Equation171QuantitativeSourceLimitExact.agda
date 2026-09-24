module DASHI.Physics.YangMills.BalabanCMP119Equation171QuantitativeSourceLimitExact where

------------------------------------------------------------------------
-- QUANTITATIVE EQ.(1.71) QUADRATURE -> CMP119 SOURCE DENSITY LIMIT
--
-- Compose:
--   finite cell error theorem
--   + vanishing oscillation/discrepancy budgets
--   + Eq.(1.71) source application meaning
-- to obtain the selected CMP119 density as the limit of Gate4 quadratures.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119FiniteDensityAssemblySemanticsExact as Assembly
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCMP122Equation171QuantitativeQuadratureLimitExact as Quant
import DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4RefinementSourceLimitExact as SourceLimit
import DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4QuadratureSliceExact as Slice
import DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4RefinementLimitExact as Limit

record CMP119Equation171QuantitativeSourceLimit
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
    (quantitative :
      Quant.CMP122Equation171QuantitativeQuadratureLimit
        {Scale = Scale} {Component = Component} {Functional = Functional}
        sourceT embedding sequenceLimit) : Set₁ where
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

open CMP119Equation171QuantitativeSourceLimit public

asSourceLimit :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional
      semantics sourceT embedding sequenceLimit quantitative} →
  CMP119Equation171QuantitativeSourceLimit
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    semantics sourceT embedding sequenceLimit quantitative →
  SourceLimit.CMP119Equation171Gate4RefinementSourceLimit
    source family semantics sourceT embedding
    (Quant.compileEquation171Gate4RefinementLimit quantitative)
asSourceLimit dataSet = record
  { SourceLimit.CMP119Equation171Gate4RefinementSourceLimit.sourceApplicationIsEquation171Mass =
      sourceApplicationIsEquation171Mass dataSet
  }

selectedCMP119DensityIsQuantitativeGate4Limit :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional
      semantics sourceT embedding sequenceLimit quantitative}
    (dataSet :
      CMP119Equation171QuantitativeSourceLimit
        {trajectory = trajectory} {split = split}
        source family
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        semantics sourceT embedding sequenceLimit quantitative)
    cutoff slow →
  Slice.embedQ embedding
    (Assembly.evaluateDensity semantics
      (Beta.densityAt source cutoff)
      slow)
  ≡
  Seq.limit sequenceLimit
    (λ refinement →
      Limit.embeddedGate4MassAt
        (Quant.compileEquation171Gate4RefinementLimit quantitative)
        refinement cutoff slow)
selectedCMP119DensityIsQuantitativeGate4Limit dataSet cutoff slow =
  SourceLimit.selectedDensityEvaluationIsGate4QuadratureLimit
    (asSourceLimit dataSet) cutoff slow

cmp119QuantitativeSourceLimitCompilerLevel : ProofLevel
cmp119QuantitativeSourceLimitCompilerLevel = machineChecked

-- Only source meaning and actual vanishing cell-error inputs remain physical.
literalCMP119ApplicationEquation171MeaningLevel : ProofLevel
literalCMP119ApplicationEquation171MeaningLevel = conditional
