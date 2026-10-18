{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3SelectedStateMassWeightedHaarExact where

------------------------------------------------------------------------
-- S3b MAX-CUT: SELECTED STATE + EXACT MASS + MASS-WEIGHTED OSCILLATION.
--
-- Combine the two existing improvements rather than paying their seams again:
--   * selected-state quadrature fixes the finite state list by construction;
--   * exact Haar cell masses erase mass discrepancy;
--   * normalized mass-weighting makes the whole finite error budget exactly
--     the one uniform oscillation modulus.
--
-- Thus the selected physical-Haar weld consumes ONE convergence theorem:
--
--   Vanishes (uniformOscillation_n).
--
-- There is no statesAt=selectedStates theorem, no independent mass discrepancy
-- sequence, and no cell-count-growth estimate on this route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119CosmologyP3SelectedStateHaarQuadratureExact as Selected
import DASHI.Physics.Foundations.CMP119CosmologyP3MassWeightedPhysicalHaarCompilerExact as WeightedCompiler
import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityApproximationExact as Approx
import DASHI.Physics.YangMills.BalabanCMP119FiniteObservableExpectationConvergenceExact as Expect
import DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact as Quad
import DASHI.Physics.YangMills.BalabanCompactHaarMassWeightedOscillationExact as Weighted
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

record SelectedStateMassWeightedHaarData
    {SlowField Sequence Component Step Cell : Set}
    (approximation :
      Approx.CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step)
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError)
    (states : List SlowField)
    (scale : Nat)
    (observable : SlowField → ℝ) : Set₁ where
  field
    weightedQuadratureAt :
      Nat → Weighted.MassWeightedExactQuadrature Cell

    physicalHaarExpectation : ℝ

    sourceIntegralIsPhysical :
      ∀ refinement →
      Quad.sourceIntegral
        (Weighted.asFiniteQuadrature (weightedQuadratureAt refinement))
      ≡ physicalHaarExpectation

    selectedSourceExpectationIsQuadrature :
      ∀ refinement →
      Expect.sourceExpectation approximation states scale observable
      ≡
      Quad.quadratureSum
        (Weighted.asFiniteQuadrature (weightedQuadratureAt refinement))

    uniformOscillationVanishes :
      Seq.Vanishes sequenceLimit
        (λ refinement →
          Weighted.uniformOscillation (weightedQuadratureAt refinement))

open SelectedStateMassWeightedHaarData public

asMassWeightedPhysicalHaarData :
  ∀ {SlowField Sequence Component Step Cell approximation sequenceLimit states scale observable} →
  SelectedStateMassWeightedHaarData
    {SlowField = SlowField} {Sequence = Sequence}
    {Component = Component} {Step = Step} {Cell = Cell}
    approximation sequenceLimit states scale observable →
  WeightedCompiler.MassWeightedPhysicalHaarData
    {SlowField = SlowField} {Sequence = Sequence}
    {Component = Component} {Step = Step} {Cell = Cell}
    approximation sequenceLimit scale observable
asMassWeightedPhysicalHaarData {states = states} data = record
  { WeightedCompiler.MassWeightedPhysicalHaarData.statesAt = λ _ → states
  ; WeightedCompiler.MassWeightedPhysicalHaarData.weightedQuadratureAt =
      weightedQuadratureAt data
  ; WeightedCompiler.MassWeightedPhysicalHaarData.physicalHaarExpectation =
      physicalHaarExpectation data
  ; WeightedCompiler.MassWeightedPhysicalHaarData.sourceIntegralIsPhysical =
      sourceIntegralIsPhysical data
  ; WeightedCompiler.MassWeightedPhysicalHaarData.sourceExpectationIsQuadrature =
      selectedSourceExpectationIsQuadrature data
  ; WeightedCompiler.MassWeightedPhysicalHaarData.uniformOscillationVanishes =
      uniformOscillationVanishes data
  }

asSelectedStatePhysicalHaarQuadrature :
  ∀ {SlowField Sequence Component Step Cell approximation sequenceLimit states scale observable} →
  SelectedStateMassWeightedHaarData
    {SlowField = SlowField} {Sequence = Sequence}
    {Component = Component} {Step = Step} {Cell = Cell}
    approximation sequenceLimit states scale observable →
  Selected.SelectedStateCMP119PhysicalHaarQuadrature
    {SlowField = SlowField} {Sequence = Sequence}
    {Component = Component} {Step = Step} {Cell = Cell}
    approximation sequenceLimit states scale observable
asSelectedStatePhysicalHaarQuadrature data = record
  { Selected.SelectedStateCMP119PhysicalHaarQuadrature.quadratureAt =
      λ refinement →
        Weighted.asFiniteQuadrature (weightedQuadratureAt data refinement)
  ; Selected.SelectedStateCMP119PhysicalHaarQuadrature.physicalHaarExpectation =
      physicalHaarExpectation data
  ; Selected.SelectedStateCMP119PhysicalHaarQuadrature.sourceIntegralIsPhysical =
      sourceIntegralIsPhysical data
  ; Selected.SelectedStateCMP119PhysicalHaarQuadrature.selectedSourceExpectationIsQuadrature =
      selectedSourceExpectationIsQuadrature data
  ; Selected.SelectedStateCMP119PhysicalHaarQuadrature.quadratureErrorVanishes =
      WeightedCompiler.quadratureBudgetVanishes
        (asMassWeightedPhysicalHaarData data)
  }

separateSelectedStateEqualityRequired : Bool
separateSelectedStateEqualityRequired = false

onlyUniformOscillationVanishingRemains : Bool
onlyUniformOscillationVanishingRemains = true

massDiscrepancyOrCellCountGrowthRequired : Bool
massDiscrepancyOrCellCountGrowthRequired = false
