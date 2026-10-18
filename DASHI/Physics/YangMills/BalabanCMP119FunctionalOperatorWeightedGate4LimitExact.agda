module DASHI.Physics.YangMills.BalabanCMP119FunctionalOperatorWeightedGate4LimitExact where

------------------------------------------------------------------------
-- FUNCTIONAL-OPERATOR CMP119 SOURCE -> WEIGHTED GATE4 LIMIT
--
-- This consumer starts from the strict source type
--
--   T_k : Action -> SlowField -> ℝ.
--
-- It deliberately does NOT identify T_k with one Eq.(1.71) component.
-- Instead the remaining source bridge is named as a factorized-T realization:
-- the result of applying the complete source T_k to A_k must be identified
-- with the corresponding complete weighted Eq.(1.71) realization.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenFunctionalDensityExact as Functional
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119FunctionalOperatorExact as CMP119
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCMP122Equation171WeightedGate4RefinementLimitExact as WeightedLimit

record CMP119FunctionalOperatorWeightedGate4Limit
    {trajectory split SlowField}
    (inputs :
      Functional.BetaDrivenFunctionalDensityInputs
        {trajectory = trajectory} {split = split} SlowField)
    (family :
      CMP119.BetaDrivenCMP119FunctionalOperatorFamily inputs)
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
    -- This is intentionally NOT described as "one component = whole T_k".
    -- A concrete inhabitant must first compile the source factorization
    -- (2.19)--(2.22) and the admissible-sequence structure of (2.18).
    factorizedTOperationApplicationIsWeightedSourceMass :
      ∀ cutoff slow →
      CMP119.operationAt family cutoff
        (CMP119.effectiveActionAt family cutoff)
        slow
      ≡
      Eq171.sourceTOperationMass sourceT cutoff slow

open CMP119FunctionalOperatorWeightedGate4Limit public

completeTOperationApplicationIsWeightedGate4Limit :
  ∀ {trajectory split SlowField inputs family
      Scale Fine Component FunctionalValue
      sourceT embedding sequenceLimit quadrature}
    (dataSet :
      CMP119FunctionalOperatorWeightedGate4Limit
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField}
        inputs family
        {Scale = Scale} {Fine = Fine}
        {Component = Component} {FunctionalValue = FunctionalValue}
        sourceT embedding sequenceLimit quadrature)
    cutoff slow →
  CMP119.operationAt family cutoff
    (CMP119.effectiveActionAt family cutoff)
    slow
  ≡
  Seq.limit sequenceLimit
    (λ refinement →
      WeightedLimit.weightedGate4MassAt
        quadrature refinement cutoff slow)
completeTOperationApplicationIsWeightedGate4Limit
  {quadrature = quadrature} dataSet cutoff slow =
  trans
    (factorizedTOperationApplicationIsWeightedSourceMass
      dataSet cutoff slow)
    (WeightedLimit.equation171SourceMassIsWeightedGate4Limit
      quadrature cutoff slow)

selectedCMP119DensityIsWeightedGate4Limit :
  ∀ {trajectory split SlowField inputs family
      Scale Fine Component FunctionalValue
      sourceT embedding sequenceLimit quadrature}
    (dataSet :
      CMP119FunctionalOperatorWeightedGate4Limit
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
selectedCMP119DensityIsWeightedGate4Limit
  {family = family} dataSet cutoff slow =
  trans
    (CMP119.selectedDensityPointwiseEquation
      family cutoff slow)
    (completeTOperationApplicationIsWeightedGate4Limit
      dataSet cutoff slow)

functionalOperatorWeightedLimitCompilerLevel : ProofLevel
functionalOperatorWeightedLimitCompilerLevel = machineChecked

functionalOperatorF1aEliminatedLevel : ProofLevel
functionalOperatorF1aEliminatedLevel = machineChecked

-- Remaining source structure, not an evaluator seam:
-- extract/compile CMP119 (2.18)--(2.22) and CMP122 (1.71) on the same
-- admissible-domain/component/one-step carrier.
literalCMP119FactorizedTOperationToEquation171Level : ProofLevel
literalCMP119FactorizedTOperationToEquation171Level = conditional
