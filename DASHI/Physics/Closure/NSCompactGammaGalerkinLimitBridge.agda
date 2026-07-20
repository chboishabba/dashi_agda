module DASHI.Physics.Closure.NSCompactGammaGalerkinLimitBridge where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption

------------------------------------------------------------------------
-- Finite-Galerkin to continuum order passage.
--
-- A cutoff-uniform estimate alone is not a continuum theorem.  The missing
-- analytic ingredients are convergence of both sides and closedness of the
-- order under that convergence.  This module states those ingredients once and
-- proves the limit passage used by the compact-Gamma/D log E lane.
--
-- Compactness, identification of the nonlinear limit, and lower
-- semicontinuity must inhabit `Converges` and `orderClosed`; finite receipts do
-- not provide them.
------------------------------------------------------------------------

record SequentialOrderClosure
    (A : AbsorptionArithmetic) : Set₁ where
  field
    Converges :
      (Nat → Scalar A) → Scalar A → Set

    orderClosed :
      {left right : Nat → Scalar A} →
      {leftLimit rightLimit : Scalar A} →
      Converges left leftLimit →
      Converges right rightLimit →
      ((cutoff : Nat) → _≤_ A (left cutoff) (right cutoff)) →
      _≤_ A leftLimit rightLimit

open SequentialOrderClosure public

record GalerkinEstimateFamily
    (A : AbsorptionArithmetic)
    (C : SequentialOrderClosure A) : Set₁ where
  field
    cutoffLeft : Nat → Scalar A
    cutoffRight : Nat → Scalar A

    continuumLeft : Scalar A
    continuumRight : Scalar A

    leftConverges : Converges C cutoffLeft continuumLeft
    rightConverges : Converges C cutoffRight continuumRight

    cutoffEstimate :
      (cutoff : Nat) →
      _≤_ A (cutoffLeft cutoff) (cutoffRight cutoff)

open GalerkinEstimateFamily public

galerkinEstimatePassesToContinuum :
  (A : AbsorptionArithmetic) →
  (C : SequentialOrderClosure A) →
  (F : GalerkinEstimateFamily A C) →
  _≤_ A (continuumLeft F) (continuumRight F)
galerkinEstimatePassesToContinuum A C F =
  orderClosed C
    (leftConverges F)
    (rightConverges F)
    (cutoffEstimate F)

------------------------------------------------------------------------
-- Named compact-Gamma specialization.  The left side is the absolute D log E
-- response and the right side is the modulus budget.  This keeps the authority
-- boundary visible at the exact finite-to-continuum seam.
------------------------------------------------------------------------

record UniformLogModulusGalerkinFamily
    (A : AbsorptionArithmetic)
    (C : SequentialOrderClosure A) : Set₁ where
  field
    cutoffAbsoluteLogDerivative : Nat → Scalar A
    cutoffLogModulusBudget : Nat → Scalar A

    continuumAbsoluteLogDerivative : Scalar A
    continuumLogModulusBudget : Scalar A

    derivativeConverges :
      Converges C
        cutoffAbsoluteLogDerivative
        continuumAbsoluteLogDerivative

    budgetConverges :
      Converges C
        cutoffLogModulusBudget
        continuumLogModulusBudget

    uniformCutoffLogModulus :
      (cutoff : Nat) →
      _≤_ A
        (cutoffAbsoluteLogDerivative cutoff)
        (cutoffLogModulusBudget cutoff)

open UniformLogModulusGalerkinFamily public

asGalerkinEstimateFamily :
  (A : AbsorptionArithmetic) →
  (C : SequentialOrderClosure A) →
  UniformLogModulusGalerkinFamily A C →
  GalerkinEstimateFamily A C
asGalerkinEstimateFamily A C F = record
  { cutoffLeft = cutoffAbsoluteLogDerivative F
  ; cutoffRight = cutoffLogModulusBudget F
  ; continuumLeft = continuumAbsoluteLogDerivative F
  ; continuumRight = continuumLogModulusBudget F
  ; leftConverges = derivativeConverges F
  ; rightConverges = budgetConverges F
  ; cutoffEstimate = uniformCutoffLogModulus F
  }

uniformLogModulusPassesToContinuum :
  (A : AbsorptionArithmetic) →
  (C : SequentialOrderClosure A) →
  (F : UniformLogModulusGalerkinFamily A C) →
  _≤_ A
    (continuumAbsoluteLogDerivative F)
    (continuumLogModulusBudget F)
uniformLogModulusPassesToContinuum A C F =
  galerkinEstimatePassesToContinuum A C
    (asGalerkinEstimateFamily A C F)
