module DASHI.Physics.Closure.NSPeriodicObservableDerivativeAlgebra where

open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- Exact symbolic differential-field laws used by all compact-Gamma observables.
--
-- This is a theorem interface for ordinary real calculus, not a Navier--Stokes
-- estimate.  The derivative modules derive packet, Gamma, off-packet and size
-- formulas from this one law owner rather than accepting unrelated identities.
------------------------------------------------------------------------

record ObservableDerivativeAlgebra (Time Scalar : Set) : Set₁ where
  field
    _+_ _-_ _*_ _/_ : Scalar → Scalar → Scalar
    negative negativeLog : Scalar → Scalar
    derivative : (Time → Scalar) → Time → Scalar

    Differentiable : (Time → Scalar) → Time → Set
    Nonzero : (Time → Scalar) → Time → Set

    differentiableAdd : ∀ f g τ →
      Differentiable f τ → Differentiable g τ →
      Differentiable (λ t → _+_ (f t) (g t)) τ

    differentiableSubtract : ∀ f g τ →
      Differentiable f τ → Differentiable g τ →
      Differentiable (λ t → _-_ (f t) (g t)) τ

    differentiableMultiply : ∀ f g τ →
      Differentiable f τ → Differentiable g τ →
      Differentiable (λ t → _*_ (f t) (g t)) τ

    differentiableDivide : ∀ f g τ →
      Differentiable f τ → Differentiable g τ → Nonzero g τ →
      Differentiable (λ t → _/_ (f t) (g t)) τ

    differentiableNegativeLog : ∀ f τ →
      Differentiable f τ → Nonzero f τ →
      Differentiable (λ t → negativeLog (f t)) τ

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
      _/_ (negative (derivative f τ)) (f τ)

open ObservableDerivativeAlgebra public
