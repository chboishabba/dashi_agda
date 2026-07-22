module DASHI.Physics.Closure.NSPeriodicSizeFunctionalDerivative where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSPeriodicObservableDerivativeAlgebra as Calculus

------------------------------------------------------------------------
-- Exact product-rule derivative for a squared size functional.
--
-- Using the squared size avoids introducing a square-root chain rule or a false
-- differentiability claim at the zero state.  A ceiling on size is equivalently a
-- ceiling on squared size once the concrete ordered-real carrier is supplied.
------------------------------------------------------------------------

record SizeSquaredDerivativeInputs
    (Time Scalar : Set)
    (A : Calculus.ObservableDerivativeAlgebra Time Scalar) : Set₁ where
  field
    sizeAmplitude : Time → Scalar
    sizeAmplitudeDifferentiable : ∀ τ →
      Calculus.Differentiable A sizeAmplitude τ

open SizeSquaredDerivativeInputs public

sizeSquared :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  SizeSquaredDerivativeInputs Time Scalar A → Time → Scalar
sizeSquared {A = A} S τ =
  Calculus._*_ A (sizeAmplitude S τ) (sizeAmplitude S τ)

sizeSquaredDifferentiable :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (S : SizeSquaredDerivativeInputs Time Scalar A) → ∀ τ →
  Calculus.Differentiable A (sizeSquared S) τ
sizeSquaredDifferentiable {A = A} S τ =
  Calculus.differentiableMultiply A
    (sizeAmplitude S)
    (sizeAmplitude S)
    τ
    (sizeAmplitudeDifferentiable S τ)
    (sizeAmplitudeDifferentiable S τ)

sizeSquaredDerivativeFormula :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  SizeSquaredDerivativeInputs Time Scalar A → Time → Scalar
sizeSquaredDerivativeFormula {A = A} S τ =
  Calculus._+_ A
    (Calculus._*_ A
      (Calculus.derivative A (sizeAmplitude S) τ)
      (sizeAmplitude S τ))
    (Calculus._*_ A
      (sizeAmplitude S τ)
      (Calculus.derivative A (sizeAmplitude S) τ))

sizeSquaredDerivative :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (S : SizeSquaredDerivativeInputs Time Scalar A) → ∀ τ →
  Calculus.derivative A (sizeSquared S) τ ≡
  sizeSquaredDerivativeFormula S τ
sizeSquaredDerivative {A = A} S τ =
  Calculus.derivativeMultiply A
    (sizeAmplitude S)
    (sizeAmplitude S)
    τ
    (sizeAmplitudeDifferentiable S τ)
    (sizeAmplitudeDifferentiable S τ)
