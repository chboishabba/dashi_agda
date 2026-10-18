{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityWeightedEquation171ExpectationCompilerExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP119Equation218FactorizedFunctionalDensityExact as Factor
import DASHI.Physics.YangMills.BalabanCMP119Equation171WeightedStepApproximationExact as Step
import DASHI.Physics.YangMills.BalabanCMP119Equation171WeightedFactorizedConvergenceExact as WeightedConv
import DASHI.Physics.YangMills.BalabanCMP119FiniteObservableExpectationConvergenceExact as Expect
import DASHI.Physics.YangMills.BalabanRealVanishingFiniteAlgebraExact as Vanishing
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed

------------------------------------------------------------------------
-- AG-S1 ANALYTIC COMPILER
--
-- Mass-exact Haar-weighted Eq.(1.71) tagged quadratures
--   -> one-step CMP119 approximation
--   -> complete factorized density convergence
--   -> finite selected observable expectation convergence.
--
-- Thus no new expectation convergence theorem belongs to the antigravity lane.
-- The remaining S1 physics is only the same-object identification of this exact
-- sourceExpectation with the literal physical Haar expectation.
------------------------------------------------------------------------

record WeightedEquation171SelectedExpectation
    {trajectory split SlowField Sequence Component StepIndex
     Scale Fine FunctionalValue : Set}
    (factorized :
      Factor.CMP119Equation218FactorizedFunctionalData
        {trajectory = trajectory} {split = split}
        SlowField Sequence Component StepIndex)
    (embedding : RingEmbed.RationalRealRingEmbedding)
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError)
    (weighted :
      Step.CMP119Equation171WeightedStepApproximation
        factorized
        {Scale = Scale} {Fine = Fine}
        {FunctionalValue = FunctionalValue}
        embedding sequenceLimit) : Set₁ where
  field
    vanishingAlgebra :
      Vanishing.RealVanishingFiniteAlgebra sequenceLimit

    states : List SlowField
    scale : Nat
    observable : SlowField → ℝ

open WeightedEquation171SelectedExpectation public

sourceExpectation :
  ∀ {trajectory split SlowField Sequence Component StepIndex
      Scale Fine FunctionalValue factorized embedding sequenceLimit weighted} →
  WeightedEquation171SelectedExpectation
    {trajectory = trajectory} {split = split}
    {SlowField = SlowField} {Sequence = Sequence}
    {Component = Component} {StepIndex = StepIndex}
    {Scale = Scale} {Fine = Fine}
    {FunctionalValue = FunctionalValue}
    factorized embedding sequenceLimit weighted →
  ℝ
sourceExpectation {weighted = weighted} input =
  Expect.sourceExpectation
    (Step.asFactorizedDensityApproximation weighted)
    (states input)
    (scale input)
    (observable input)

approximateExpectation :
  ∀ {trajectory split SlowField Sequence Component StepIndex
      Scale Fine FunctionalValue factorized embedding sequenceLimit weighted} →
  WeightedEquation171SelectedExpectation
    {trajectory = trajectory} {split = split}
    {SlowField = SlowField} {Sequence = Sequence}
    {Component = Component} {StepIndex = StepIndex}
    {Scale = Scale} {Fine = Fine}
    {FunctionalValue = FunctionalValue}
    factorized embedding sequenceLimit weighted →
  Nat → ℝ
approximateExpectation {weighted = weighted} input refinement =
  Expect.approximateExpectation
    (Step.asFactorizedDensityApproximation weighted)
    (states input)
    refinement
    (scale input)
    (observable input)

weightedEquation171ExpectationConverges :
  ∀ {trajectory split SlowField Sequence Component StepIndex
      Scale Fine FunctionalValue factorized embedding sequenceLimit weighted}
    (input :
      WeightedEquation171SelectedExpectation
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField} {Sequence = Sequence}
        {Component = Component} {StepIndex = StepIndex}
        {Scale = Scale} {Fine = Fine}
        {FunctionalValue = FunctionalValue}
        factorized embedding sequenceLimit weighted) →
  sourceExpectation input
  ≡
  Seq.limit sequenceLimit (approximateExpectation input)
weightedEquation171ExpectationConverges
    {weighted = weighted}
    {sequenceLimit = sequenceLimit}
    input =
  Expect.finiteObservableExpectationConverges
    (WeightedConv.compileCompleteCMP119DensityConvergence
      weighted (vanishingAlgebra input))
    (vanishingAlgebra input)
    (states input)
    (scale input)
    (observable input)

weightedEquation171SelectedExpectationCompilerLevel : ProofLevel
weightedEquation171SelectedExpectationCompilerLevel = machineChecked

newAntigravityExpectationConvergenceAnalysisRequired : Bool
newAntigravityExpectationConvergenceAnalysisRequired = false
