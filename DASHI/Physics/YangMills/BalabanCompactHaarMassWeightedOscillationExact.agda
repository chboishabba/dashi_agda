{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCompactHaarMassWeightedOscillationExact where

------------------------------------------------------------------------
-- MASS-WEIGHTED OSCILLATION -> ONE GLOBAL MODULUS.
--
-- After choosing exact source/Haar cell masses as quadrature weights, the only
-- cell error is representative oscillation.  If on every cell C
--
--   | integral_C f - mu(C) f(x_C) | <= mu(C) * omega,
--
-- and the finite cell masses sum to one, then the full quadrature error is
-- bounded by omega itself.  In particular the number of cells never appears.
--
-- This is the finite probability-partition theorem needed by the product-Haar
-- route: geometric refinement only has to make ONE uniform cell oscillation
-- modulus tend to zero.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 1ℝ; _+ℝ_; _*ℝ_; absℝ; _-ℝ_; _≤ℝ_;
   *-comm; *-distribʳ-+; mulOneʳ; mulZeroˡ; +-identityʳ)

import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Sums
import DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact as Quad
import DASHI.Physics.YangMills.BalabanCompactHaarExactMassQuadratureExact as ExactMass

------------------------------------------------------------------------
-- Finite-sum algebra.
------------------------------------------------------------------------

realSumPointwiseCong :
  ∀ {A : Set}
    (values : List A)
    (left right : A → ℝ) →
  (∀ x → left x ≡ right x) →
  Sums.realSum values left ≡ Sums.realSum values right
realSumPointwiseCong [] left right pointwise = refl
realSumPointwiseCong (x ∷ xs) left right pointwise =
  cong₂ _+ℝ_
    (pointwise x)
    (realSumPointwiseCong xs left right pointwise)

realSumMulRight :
  ∀ {A : Set}
    (values : List A)
    (value : A → ℝ)
    (scalar : ℝ) →
  Sums.realSum values (λ x → value x *ℝ scalar)
  ≡
  Sums.realSum values value *ℝ scalar
realSumMulRight [] value scalar =
  sym (mulZeroˡ scalar)
realSumMulRight (x ∷ xs) value scalar =
  trans
    (cong
      (λ tail → value x *ℝ scalar +ℝ tail)
      (realSumMulRight xs value scalar))
    (sym
      (*-distribʳ-+
        (value x)
        (Sums.realSum xs value)
        scalar))

------------------------------------------------------------------------
-- Exact-mass, mass-weighted quadrature data.
------------------------------------------------------------------------

record MassWeightedExactQuadrature (Cell : Set) : Set₁ where
  field
    cells : List Cell
    sourceCellIntegral : Cell → ℝ
    sourceCellMass : Cell → ℝ
    sampleValue : Cell → ℝ

    uniformOscillation : ℝ

    cellOscillationBound : ∀ cell →
      absℝ
        (sourceCellIntegral cell
          -ℝ (sourceCellMass cell *ℝ sampleValue cell))
      ≤ℝ sourceCellMass cell *ℝ uniformOscillation

    massesNormalize :
      Sums.realSum cells sourceCellMass ≡ 1ℝ

open MassWeightedExactQuadrature public

asExactMassQuadrature :
  ∀ {Cell} →
  MassWeightedExactQuadrature Cell →
  ExactMass.ExactMassQuadratureData Cell
asExactMassQuadrature data = record
  { ExactMass.ExactMassQuadratureData.cells = cells data
  ; ExactMass.ExactMassQuadratureData.sourceCellIntegral =
      sourceCellIntegral data
  ; ExactMass.ExactMassQuadratureData.sourceCellMass = sourceCellMass data
  ; ExactMass.ExactMassQuadratureData.sampleValue = sampleValue data
  ; ExactMass.ExactMassQuadratureData.oscillationError =
      λ cell → sourceCellMass data cell *ℝ uniformOscillation data
  ; ExactMass.ExactMassQuadratureData.oscillationBound =
      cellOscillationBound data
  }

asFiniteQuadrature :
  ∀ {Cell} →
  MassWeightedExactQuadrature Cell →
  Quad.FiniteQuadratureCellError Cell
asFiniteQuadrature data =
  ExactMass.asFiniteQuadratureCellError (asExactMassQuadrature data)

massWeightedTotalBudgetIsUniformOscillation :
  ∀ {Cell}
    (data : MassWeightedExactQuadrature Cell) →
  Quad.totalErrorBudget (asFiniteQuadrature data)
  ≡ uniformOscillation data
massWeightedTotalBudgetIsUniformOscillation data =
  let
    q = asFiniteQuadrature data
    omega = uniformOscillation data

    eraseZero :
      Sums.realSum (cells data)
        (λ cell →
          sourceCellMass data cell *ℝ omega +ℝ
          Quad.discrepancyError q cell)
      ≡
      Sums.realSum (cells data)
        (λ cell → sourceCellMass data cell *ℝ omega)
    eraseZero =
      realSumPointwiseCong
        (cells data)
        (λ cell →
          sourceCellMass data cell *ℝ omega +ℝ
          Quad.discrepancyError q cell)
        (λ cell → sourceCellMass data cell *ℝ omega)
        (λ cell → +-identityʳ (sourceCellMass data cell *ℝ omega))

    factorOmega :
      Sums.realSum (cells data)
        (λ cell → sourceCellMass data cell *ℝ omega)
      ≡
      Sums.realSum (cells data) (sourceCellMass data) *ℝ omega
    factorOmega = realSumMulRight (cells data) (sourceCellMass data) omega

    normalize :
      Sums.realSum (cells data) (sourceCellMass data) *ℝ omega
      ≡ omega
    normalize =
      trans
        (cong (λ mass → mass *ℝ omega) (massesNormalize data))
        (trans (*-comm 1ℝ omega) (mulOneʳ omega))
  in
  trans eraseZero (trans factorOmega normalize)

massWeightedQuadratureErrorBound :
  ∀ {Cell}
    (data : MassWeightedExactQuadrature Cell) →
  absℝ
    (Quad.sourceIntegral (asFiniteQuadrature data)
      -ℝ Quad.quadratureSum (asFiniteQuadrature data))
  ≤ℝ uniformOscillation data
massWeightedQuadratureErrorBound data =
  subst
    (λ budget →
      absℝ
        (Quad.sourceIntegral (asFiniteQuadrature data)
          -ℝ Quad.quadratureSum (asFiniteQuadrature data))
      ≤ℝ budget)
    (massWeightedTotalBudgetIsUniformOscillation data)
    (Quad.finiteQuadratureErrorBound (asFiniteQuadrature data))

cellCountDoesNotEnterMassWeightedGlobalBound : Bool
cellCountDoesNotEnterMassWeightedGlobalBound = true

massWeightedOscillationReducesGlobalErrorToOneModulus : Bool
massWeightedOscillationReducesGlobalErrorToOneModulus = true

independentCellCountGrowthEstimateRequired : Bool
independentCellCountGrowthEstimateRequired = false
