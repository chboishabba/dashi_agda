{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCompactHaarExactMassQuadratureExact where

------------------------------------------------------------------------
-- EXACT-MASS HAAR QUADRATURE.
--
-- The generic finite-quadrature theorem separates cell oscillation error from
-- cell-mass discrepancy.  For Haar quadrature there is no reason to approximate
-- the mass of a chosen measurable cell: use its exact Haar/source mass as the
-- quadrature weight.  Then the discrepancy summand vanishes definitionally up
-- to the ordinary real identities |x-x| = 0.
--
-- Thus the physical/geometric convergence problem can be cut to shrinking-cell
-- oscillation (plus construction of the cells and their exact Haar masses).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _-ℝ_; absℝ; _≤ℝ_; ≤ℝ-refl; subSelf; absZero)

import DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact as Quad

record ExactMassQuadratureData (Cell : Set) : Set₁ where
  field
    cells : List Cell
    sourceCellIntegral : Cell → ℝ
    sourceCellMass : Cell → ℝ
    sampleValue : Cell → ℝ

    oscillationError : Cell → ℝ
    oscillationBound : ∀ cell →
      absℝ
        (sourceCellIntegral cell
          -ℝ (sourceCellMass cell *ℝ sampleValue cell))
      ≤ℝ oscillationError cell

open ExactMassQuadratureData public

zeroDiscrepancyBound :
  ∀ {Cell} (data : ExactMassQuadratureData Cell) cell →
  absℝ
    ((sourceCellMass data cell *ℝ sampleValue data cell)
      -ℝ (sourceCellMass data cell *ℝ sampleValue data cell))
  ≤ℝ 0ℝ
zeroDiscrepancyBound data cell =
  let value = sourceCellMass data cell *ℝ sampleValue data cell
  in
  subst
    (λ difference → absℝ difference ≤ℝ 0ℝ)
    (sym (subSelf value))
    (subst
      (λ absolute → absolute ≤ℝ 0ℝ)
      (sym absZero)
      ≤ℝ-refl)

asFiniteQuadratureCellError :
  ∀ {Cell} →
  ExactMassQuadratureData Cell →
  Quad.FiniteQuadratureCellError Cell
asFiniteQuadratureCellError data = record
  { Quad.FiniteQuadratureCellError.cells = cells data
  ; Quad.FiniteQuadratureCellError.sourceCellIntegral = sourceCellIntegral data
  ; Quad.FiniteQuadratureCellError.sourceCellMass = sourceCellMass data
  ; Quad.FiniteQuadratureCellError.quadratureCellMass = sourceCellMass data
  ; Quad.FiniteQuadratureCellError.sampleValue = sampleValue data
  ; Quad.FiniteQuadratureCellError.oscillationError = oscillationError data
  ; Quad.FiniteQuadratureCellError.discrepancyError = λ _ → 0ℝ
  ; Quad.FiniteQuadratureCellError.oscillationBound = oscillationBound data
  ; Quad.FiniteQuadratureCellError.discrepancyBound = zeroDiscrepancyBound data
  }

exactCellMassEliminatesMassDiscrepancy : Bool
exactCellMassEliminatesMassDiscrepancy = true

onlyCellOscillationRemainsAfterExactMassChoice : Bool
onlyCellOscillationRemainsAfterExactMassChoice = true

independentMassDiscrepancyEstimateRequired : Bool
independentMassDiscrepancyEstimateRequired = false
