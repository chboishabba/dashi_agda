module DASHI.Physics.YangMills.BalabanCMP119FunctionalEquation171WeightedGate4SourceLimitExact where

------------------------------------------------------------------------
-- FUNCTIONAL CMP119 DENSITY -> LITERAL EQ.(1.71) -> WEIGHTED GATE4 LIMIT
--
-- Source side is real-valued throughout.  No rational evaluator and no
-- rational->real embedding are inserted between rho_k and the Eq.(1.71) mass.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenFunctionalDensityExact as Functional
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119FunctionalResidualFamilyExact as CMP119
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCMP122Equation171WeightedGate4RefinementLimitExact as WeightedLimit

record CMP119FunctionalEquation171WeightedGate4SourceLimit
    {trajectory split SlowField}
    (inputs :
      Functional.BetaDrivenFunctionalDensityInputs
        {trajectory = trajectory} {split = split} SlowField)
    (family :
      CMP119.BetaDrivenCMP119FunctionalResidualFamily inputs)
    {Scale Fine Component FunctionalValue : Set}
    (sourceT :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField)
    (embedding :
      RingEmbed.RationalRealRingEmbedding)
    (sequenceLimit :
      Seq.RealSequenceLimitByVanishingError)
    (quadrature :
      WeightedLimit.Equation171WeightedGate4RefinementLimit
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = FunctionalValue}
        sourceT embedding sequenceLimit) : Set₁ where
  field
    -- F1b-1 in its correct scalar type.
    sourceApplicationIsEquation171Mass :
      ∀ cutoff slow →
      CMP119.applyOperationAction family
        (CMP119.operationAt family cutoff)
        (CMP119.effectiveActionAt family cutoff)
        slow
      ≡
      Eq171.sourceTOperationMass sourceT cutoff slow

open CMP119FunctionalEquation171WeightedGate4SourceLimit public

sourceApplicationIsWeightedGate4Limit :
  ∀ {trajectory split SlowField inputs family
      Scale Fine Component FunctionalValue
      sourceT embedding sequenceLimit quadrature}
    (dataSet :
      CMP119FunctionalEquation171WeightedGate4SourceLimit
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField}
        inputs family
        {Scale = Scale} {Fine = Fine}
        {Component = Component} {FunctionalValue = FunctionalValue}
        sourceT embedding sequenceLimit quadrature)
    cutoff slow →
  CMP119.applyOperationAction family
    (CMP119.operationAt family cutoff)
    (CMP119.effectiveActionAt family cutoff)
    slow
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

selectedFunctionalDensityIsWeightedGate4Limit :
  ∀ {trajectory split SlowField inputs family
      Scale Fine Component FunctionalValue
      sourceT embedding sequenceLimit quadrature}
    (dataSet :
      CMP119FunctionalEquation171WeightedGate4SourceLimit
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField}
        inputs family
        {Scale = Scale} {Fine = Fine}
        {Component = Component} {FunctionalValue = FunctionalValue}
        sourceT embedding sequenceLimit quadrature)
    cutoff slow →
  Functional.densityAt inputs cutoff slow
  ≡
  Seq.limit sequenceLimit
    (λ refinement →
      WeightedLimit.weightedGate4MassAt
        quadrature refinement cutoff slow)
selectedFunctionalDensityIsWeightedGate4Limit
  {family = family} dataSet cutoff slow =
  trans
    (CMP119.selectedDensityPointwiseEquation
      family cutoff slow)
    (sourceApplicationIsWeightedGate4Limit
      dataSet cutoff slow)

functionalCMP119WeightedSourceLimitCompilerLevel : ProofLevel
functionalCMP119WeightedSourceLimitCompilerLevel = machineChecked

functionalCMP119F1aEliminatedLevel : ProofLevel
functionalCMP119F1aEliminatedLevel = machineChecked

-- Remaining source seam: Eq.(2.18)'s selected T_k/A_k application must be the
-- literal Eq.(1.71) component mass after the source's factorized one-step
-- operations and admissible-domain sums are specialized.
literalCMP119ApplicationIsEquation171MassFunctionalLevel : ProofLevel
literalCMP119ApplicationIsEquation171MassFunctionalLevel = conditional
