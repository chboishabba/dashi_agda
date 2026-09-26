{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityEquation171ContributionExpectationCompilerExact where

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Foundations.CMP119AntigravityEquation171ContributionStepApproximationExact as Step
import DASHI.Physics.YangMills.BalabanCMP119Equation218FactorizedFunctionalDensityExact as Factor
import DASHI.Physics.YangMills.BalabanCMP119FactorizedMarkedBudgetVanishesExact as Budget
import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityConvergenceExact as Convergence
import DASHI.Physics.YangMills.BalabanCMP119FiniteObservableExpectationConvergenceExact as Expect
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanRealVanishingFiniteAlgebraExact as Vanishing

------------------------------------------------------------------------
-- CORRECTED S1 COMPILER
--
-- Two physical Eq.(1.71) moduli
--   -> one-step errors
--   -> complete factorized CMP119 density convergence
--   -> selected finite-observable expectation convergence.
------------------------------------------------------------------------

record ContributionExpectationInputs
    {trajectory split SlowField Sequence Component StepIndex
     Scale Fine FunctionalValue : Set}
    (factorized :
      Factor.CMP119Equation218FactorizedFunctionalData
        {trajectory = trajectory} {split = split}
        SlowField Sequence Component StepIndex)
    (embedding : RingEmbed.RationalRealRingEmbedding)
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError)
    (step :
      Step.CMP119Equation171ContributionStepApproximation
        factorized
        {Scale = Scale} {Fine = Fine}
        {FunctionalValue = FunctionalValue}
        embedding sequenceLimit) : Set₁ where
  field
    markedNonnegative :
      Step.ContributionMarkedNonnegative step

    vanishingAlgebra :
      Vanishing.RealVanishingFiniteAlgebra sequenceLimit

    states : List SlowField
    scale : Nat
    observable : SlowField → ℝ

open ContributionExpectationInputs public

approximation :
  ∀ {trajectory split SlowField Sequence Component StepIndex
      Scale Fine FunctionalValue factorized embedding sequenceLimit step} →
  ContributionExpectationInputs
    {trajectory = trajectory} {split = split}
    {SlowField = SlowField} {Sequence = Sequence}
    {Component = Component} {StepIndex = StepIndex}
    {Scale = Scale} {Fine = Fine}
    {FunctionalValue = FunctionalValue}
    factorized embedding sequenceLimit step →
  DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityApproximationExact.CMP119FactorizedDensityApproximation
    SlowField Sequence Component StepIndex
approximation {step = step} input =
  Step.asFactorizedDensityApproximation
    step
    (markedNonnegative input)

stepMarkedVanishing :
  ∀ {trajectory split SlowField Sequence Component StepIndex
      Scale Fine FunctionalValue factorized embedding sequenceLimit step}
    (input :
      ContributionExpectationInputs
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField} {Sequence = Sequence}
        {Component = Component} {StepIndex = StepIndex}
        {Scale = Scale} {Fine = Fine}
        {FunctionalValue = FunctionalValue}
        factorized embedding sequenceLimit step) →
  Budget.CMP119FactorizedStepMarkedVanishing
    (approximation input)
    sequenceLimit
    (vanishingAlgebra input)
stepMarkedVanishing {step = step} input = record
  { Budget.CMP119FactorizedStepMarkedVanishing.stepMarkedVanishes =
      Step.markedMajorantVanishes step
  }

densityConvergence :
  ∀ {trajectory split SlowField Sequence Component StepIndex
      Scale Fine FunctionalValue factorized embedding sequenceLimit step}
    (input :
      ContributionExpectationInputs
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField} {Sequence = Sequence}
        {Component = Component} {StepIndex = StepIndex}
        {Scale = Scale} {Fine = Fine}
        {FunctionalValue = FunctionalValue}
        factorized embedding sequenceLimit step) →
  Convergence.CMP119FactorizedDensityConvergence
    (approximation input)
    sequenceLimit
densityConvergence input =
  Budget.compileFactorizedDensityConvergence
    (stepMarkedVanishing input)

sourceExpectation :
  ∀ {trajectory split SlowField Sequence Component StepIndex
      Scale Fine FunctionalValue factorized embedding sequenceLimit step} →
  ContributionExpectationInputs
    {trajectory = trajectory} {split = split}
    {SlowField = SlowField} {Sequence = Sequence}
    {Component = Component} {StepIndex = StepIndex}
    {Scale = Scale} {Fine = Fine}
    {FunctionalValue = FunctionalValue}
    factorized embedding sequenceLimit step →
  ℝ
sourceExpectation input =
  Expect.sourceExpectation
    (approximation input)
    (states input)
    (scale input)
    (observable input)

approximateExpectation :
  ∀ {trajectory split SlowField Sequence Component StepIndex
      Scale Fine FunctionalValue factorized embedding sequenceLimit step} →
  ContributionExpectationInputs
    {trajectory = trajectory} {split = split}
    {SlowField = SlowField} {Sequence = Sequence}
    {Component = Component} {StepIndex = StepIndex}
    {Scale = Scale} {Fine = Fine}
    {FunctionalValue = FunctionalValue}
    factorized embedding sequenceLimit step →
  Nat → ℝ
approximateExpectation input refinement =
  Expect.approximateExpectation
    (approximation input)
    (states input)
    refinement
    (scale input)
    (observable input)

correctedContributionExpectationConverges :
  ∀ {trajectory split SlowField Sequence Component StepIndex
      Scale Fine FunctionalValue factorized embedding sequenceLimit step}
    (input :
      ContributionExpectationInputs
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField} {Sequence = Sequence}
        {Component = Component} {StepIndex = StepIndex}
        {Scale = Scale} {Fine = Fine}
        {FunctionalValue = FunctionalValue}
        factorized embedding sequenceLimit step) →
  sourceExpectation input
  ≡
  Seq.limit sequenceLimit (approximateExpectation input)
correctedContributionExpectationConverges input =
  Expect.finiteObservableExpectationConverges
    (densityConvergence input)
    (vanishingAlgebra input)
    (states input)
    (scale input)
    (observable input)

correctedContributionExpectationCompilerLevel : ProofLevel
correctedContributionExpectationCompilerLevel = machineChecked
