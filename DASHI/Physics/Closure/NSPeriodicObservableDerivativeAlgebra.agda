module DASHI.Physics.Closure.NSPeriodicObservableDerivativeAlgebra where

open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- Exact symbolic differential-field laws used by all four boundary observables.
--
-- This is a theorem interface for ordinary real calculus, not a Navier--Stokes
-- estimate.  The subsequent modules derive the packet, Gamma, quotient and size
-- formulas from these laws rather than accepting four unrelated derivative facts.
------------------------------------------------------------------------

record ObservableDerivativeAlgebra (Time Scalar : Set) : Set₁ where
  field
    _+_ _-_ _*_ _/_ : Scalar → Scalar → Scalar
    negativeLog : Scalar → Scalar
    derivative : (Time → Scalar) → Time → Scalar

    Differentiable : (Time → Scalar) → Time → Set
    Nonzero : (Time → Scalar) → Time → Set

    derivativeAdd : ∀ f g τ →
      Differentiable f τ → Differentiable g τ →
      derivative (λ t → _+_ (f t) (g t)) τ ≡
      _+_ (derivative f τ) (derivative g τ)

    derivativeSubtract : ∀ f g τ →
      Differentiable f τ → Differentiable g τ →
      derivative (λ t → _-_ (f t) (g t)) τ ≡
      _-_ (derivative f τ) (derivative g τ)

    derivativeMultiply : ∀ f g τ →
      Differentiable f τ → Differentiable g τ →
      derivative (λ t → _*_ (f t) (g t)) τ ≡
      _+_
        (_*_ (derivative f τ) (g τ))
        (_*_ (f τ) (derivative g τ))

    derivativeDivide : ∀ f g τ →
      Differentiable f τ → Differentiable g τ → Nonzero g τ →
      derivative (λ t → _/_ (f t) (g t)) τ ≡
      _/_
        (_-_
          (_*_ (derivative f τ) (g τ))
          (_*_ (f τ) (derivative g τ)))
        (_*_ (g τ) (g τ))

    derivativeNegativeLog : ∀ f τ →
      Differentiable f τ → Nonzero f τ →
      derivative (λ t → negativeLog (f t)) τ ≡
      _/_ (derivative f τ) (f τ)

open ObservableDerivativeAlgebra public
