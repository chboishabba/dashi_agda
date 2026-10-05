{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3MassWeightedPhysicalHaarCompilerExact where

------------------------------------------------------------------------
-- MASS-WEIGHTED PRODUCT-HAAR COMPILER.
--
-- The generic physical-Haar weld asks separately that the finite quadrature
-- total-error budget vanish.  Exact Haar cell masses plus the mass-weighted
-- oscillation theorem make that redundant: for each refinement n,
--
--   totalErrorBudget_n = uniformOscillation_n.
--
-- Hence `Vanishes uniformOscillation` is the only convergence payment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119AntigravitySourceExpectationToPhysicalHaarExact as Haar
import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityApproximationExact as Approx
import DASHI.Physics.YangMills.BalabanCMP119FiniteObservableExpectationConvergenceExact as Expect
import DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact as Quad
import DASHI.Physics.YangMills.BalabanCompactHaarMassWeightedOscillationExact as Weighted
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

record MassWeightedPhysicalHaarData
    {SlowField Sequence Component Step Cell : Set}
    (approximation :
      Approx.CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step)
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError)
    (scale : Nat)
    (observable : SlowField → ℝ) : Set₁ where
  field
    statesAt : Nat → List SlowField

    weightedQuadratureAt :
      Nat → Weighted.MassWeightedExactQuadrature Cell

    physicalHaarExpectation : ℝ

    sourceIntegralIsPhysical :
      ∀ refinement →
      Quad.sourceIntegral
        (Weighted.asFiniteQuadrature
          (weightedQuadratureAt refinement))
      ≡ physicalHaarExpectation

    sourceExpectationIsQuadrature :
      ∀ refinement →
      Expect.sourceExpectation
        approximation (statesAt refinement) scale observable
      ≡
      Quad.quadratureSum
        (Weighted.asFiniteQuadrature
          (weightedQuadratureAt refinement))

    uniformOscillationVanishes :
      Seq.Vanishes sequenceLimit
        (λ refinement →
          Weighted.uniformOscillation
            (weightedQuadratureAt refinement))

open MassWeightedPhysicalHaarData public

quadratureBudgetIsUniformOscillation :
  ∀ {SlowField Sequence Component Step Cell approximation sequenceLimit scale observable}
    (data :
      MassWeightedPhysicalHaarData
        {SlowField = SlowField}
        {Sequence = Sequence}
        {Component = Component}
        {Step = Step}
        {Cell = Cell}
        approximation sequenceLimit scale observable) →
  ∀ refinement →
  Quad.totalErrorBudget
    (Weighted.asFiniteQuadrature
      (weightedQuadratureAt data refinement))
  ≡
  Weighted.uniformOscillation
    (weightedQuadratureAt data refinement)
quadratureBudgetIsUniformOscillation data refinement =
  Weighted.massWeightedTotalBudgetIsUniformOscillation
    (weightedQuadratureAt data refinement)

quadratureBudgetVanishes :
  ∀ {SlowField Sequence Component Step Cell approximation sequenceLimit scale observable}
    (data :
      MassWeightedPhysicalHaarData
        {SlowField = SlowField}
        {Sequence = Sequence}
        {Component = Component}
        {Step = Step}
        {Cell = Cell}
        approximation sequenceLimit scale observable) →
  Seq.Vanishes sequenceLimit
    (λ refinement →
      Quad.totalErrorBudget
        (Weighted.asFiniteQuadrature
          (weightedQuadratureAt data refinement)))
quadratureBudgetVanishes {sequenceLimit = sequenceLimit} data =
  Seq.vanishesCongruent sequenceLimit
    (λ refinement →
      Weighted.uniformOscillation
        (weightedQuadratureAt data refinement))
    (λ refinement →
      Quad.totalErrorBudget
        (Weighted.asFiniteQuadrature
          (weightedQuadratureAt data refinement)))
    (λ refinement →
      Relation.Binary.PropositionalEquality.sym
        (quadratureBudgetIsUniformOscillation data refinement))
    (uniformOscillationVanishes data)

asPhysicalHaarWeld :
  ∀ {SlowField Sequence Component Step Cell approximation sequenceLimit scale observable} →
  MassWeightedPhysicalHaarData
    {SlowField = SlowField}
    {Sequence = Sequence}
    {Component = Component}
    {Step = Step}
    {Cell = Cell}
    approximation sequenceLimit scale observable →
  Haar.CMP119PhysicalHaarQuadratureWeld
    {SlowField = SlowField}
    {Sequence = Sequence}
    {Component = Component}
    {Step = Step}
    {Cell = Cell}
    approximation sequenceLimit scale observable
asPhysicalHaarWeld data = record
  { Haar.CMP119PhysicalHaarQuadratureWeld.statesAt = statesAt data
  ; Haar.CMP119PhysicalHaarQuadratureWeld.quadratureAt =
      λ refinement →
        Weighted.asFiniteQuadrature
          (weightedQuadratureAt data refinement)
  ; Haar.CMP119PhysicalHaarQuadratureWeld.physicalHaarExpectation =
      physicalHaarExpectation data
  ; Haar.CMP119PhysicalHaarQuadratureWeld.sourceIntegralIsPhysical =
      sourceIntegralIsPhysical data
  ; Haar.CMP119PhysicalHaarQuadratureWeld.sourceExpectationIsQuadrature =
      sourceExpectationIsQuadrature data
  ; Haar.CMP119PhysicalHaarQuadratureWeld.quadratureErrorVanishes =
      quadratureBudgetVanishes data
  }

uniformMassWeightedOscillationIsSufficientForHaarConvergence : Bool
uniformMassWeightedOscillationIsSufficientForHaarConvergence = true

independentQuadratureBudgetVanishingRequired : Bool
independentQuadratureBudgetVanishingRequired = false
