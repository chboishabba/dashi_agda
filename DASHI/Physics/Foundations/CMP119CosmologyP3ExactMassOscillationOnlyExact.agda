{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3ExactMassOscillationOnlyExact where

------------------------------------------------------------------------
-- S3b NEW MATH: EXACT HAAR CELL MASSES REMOVE THE SECOND ERROR SEQUENCE.
--
-- `BalabanCompactHaarExactMassQuadratureExact` already chooses the quadrature
-- mass of each cell to be its exact source/Haar mass.  Its generic quadrature
-- record therefore has discrepancyError = 0 pointwise.  Here we prove the
-- stronger sequence-level statement needed by the physical-Haar limit:
--
--   totalErrorBudget(exact-mass quadrature)
--     = sum(cell oscillation errors).
--
-- Consequently one vanishing theorem for shrinking-cell oscillation is enough
-- to inhabit the selected-state physical-Haar quadrature package.  No separate
-- mass-discrepancy convergence hypothesis survives S3b.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; +-identityʳ)

import DASHI.Physics.Foundations.CMP119CosmologyP3SelectedStateHaarQuadratureExact as Selected
import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityApproximationExact as Approx
import DASHI.Physics.YangMills.BalabanCMP119FiniteObservableExpectationConvergenceExact as Expect
import DASHI.Physics.YangMills.BalabanCompactHaarExactMassQuadratureExact as ExactMass
import DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact as Quad
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Sums
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

oscillationBudget :
  ∀ {Cell} → ExactMass.ExactMassQuadratureData Cell → ℝ
oscillationBudget data =
  Sums.realSum (ExactMass.cells data) (ExactMass.oscillationError data)

realSumPlusZeroRight :
  ∀ {A : Set} (values : List A) (value : A → ℝ) →
  Sums.realSum values (λ x → value x +ℝ 0ℝ)
  ≡ Sums.realSum values value
realSumPlusZeroRight [] value = refl
realSumPlusZeroRight (x ∷ xs) value =
  trans
    (cong
      (λ tail → (value x +ℝ 0ℝ) +ℝ tail)
      (realSumPlusZeroRight xs value))
    (cong
      (λ head → head +ℝ Sums.realSum xs value)
      (+-identityʳ (value x)))

exactMassTotalErrorBudgetIsOscillationBudget :
  ∀ {Cell} (data : ExactMass.ExactMassQuadratureData Cell) →
  Quad.totalErrorBudget (ExactMass.asFiniteQuadratureCellError data)
  ≡ oscillationBudget data
exactMassTotalErrorBudgetIsOscillationBudget data =
  realSumPlusZeroRight
    (ExactMass.cells data)
    (ExactMass.oscillationError data)

oscillationVanishesImpliesExactMassTotalBudgetVanishes :
  ∀ {Cell}
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError)
    (quadratureAt : Nat → ExactMass.ExactMassQuadratureData Cell) →
  Seq.Vanishes sequenceLimit
    (λ refinement → oscillationBudget (quadratureAt refinement)) →
  Seq.Vanishes sequenceLimit
    (λ refinement →
      Quad.totalErrorBudget
        (ExactMass.asFiniteQuadratureCellError (quadratureAt refinement)))
oscillationVanishesImpliesExactMassTotalBudgetVanishes
    sequenceLimit quadratureAt oscillationVanishes =
  Seq.vanishesCongruent sequenceLimit
    (λ refinement → oscillationBudget (quadratureAt refinement))
    (λ refinement →
      Quad.totalErrorBudget
        (ExactMass.asFiniteQuadratureCellError (quadratureAt refinement)))
    (λ refinement →
      sym (exactMassTotalErrorBudgetIsOscillationBudget
        (quadratureAt refinement)))
    oscillationVanishes

fromExactMassOscillationOnly :
  ∀ {SlowField Sequence Component Step Cell : Set}
    (approximation :
      Approx.CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step)
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError)
    (states : List SlowField)
    (scale : Nat)
    (observable : SlowField → ℝ)
    (quadratureAt : Nat → ExactMass.ExactMassQuadratureData Cell)
    (physicalHaarExpectation : ℝ) →
    (∀ refinement →
      Quad.sourceIntegral
        (ExactMass.asFiniteQuadratureCellError (quadratureAt refinement))
      ≡ physicalHaarExpectation) →
    (∀ refinement →
      Expect.sourceExpectation approximation states scale observable
      ≡ Quad.quadratureSum
          (ExactMass.asFiniteQuadratureCellError (quadratureAt refinement))) →
    Seq.Vanishes sequenceLimit
      (λ refinement → oscillationBudget (quadratureAt refinement)) →
  Selected.SelectedStateCMP119PhysicalHaarQuadrature
    {SlowField = SlowField}
    {Sequence = Sequence}
    {Component = Component}
    {Step = Step}
    {Cell = Cell}
    approximation sequenceLimit states scale observable
fromExactMassOscillationOnly
    approximation sequenceLimit states scale observable
    quadratureAt physicalHaarExpectation
    sourceIntegralIsPhysical selectedSourceExpectationIsQuadrature
    oscillationVanishes = record
  { Selected.SelectedStateCMP119PhysicalHaarQuadrature.quadratureAt =
      λ refinement →
        ExactMass.asFiniteQuadratureCellError (quadratureAt refinement)
  ; Selected.SelectedStateCMP119PhysicalHaarQuadrature.physicalHaarExpectation =
      physicalHaarExpectation
  ; Selected.SelectedStateCMP119PhysicalHaarQuadrature.sourceIntegralIsPhysical =
      sourceIntegralIsPhysical
  ; Selected.SelectedStateCMP119PhysicalHaarQuadrature.selectedSourceExpectationIsQuadrature =
      selectedSourceExpectationIsQuadrature
  ; Selected.SelectedStateCMP119PhysicalHaarQuadrature.quadratureErrorVanishes =
      oscillationVanishesImpliesExactMassTotalBudgetVanishes
        sequenceLimit quadratureAt oscillationVanishes
  }

exactMassTotalBudgetIsOscillationOnly : Bool
exactMassTotalBudgetIsOscillationOnly = true

independentMassDiscrepancyVanishesRequired : Bool
independentMassDiscrepancyVanishesRequired = false

selectedHaarClosureConsumesOnlyOscillationVanishes : Bool
selectedHaarClosureConsumesOnlyOscillationVanishes = true
