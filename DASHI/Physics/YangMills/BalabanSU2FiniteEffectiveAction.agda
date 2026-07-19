module DASHI.Physics.YangMills.BalabanSU2FiniteEffectiveAction where

open import Agda.Builtin.Equality using (_≡_; refl)

record FiniteEffectiveAction (Background Scalar : Set) : Set₁ where
  field
    gaussianDeterminant interactionCumulant constraintJacobian
      gaugeFixingNormalization irrelevantRemainder : Background → Scalar
    add : Scalar → Scalar → Scalar

open FiniteEffectiveAction public

effectiveAction :
  ∀ {Background Scalar} →
  FiniteEffectiveAction Background Scalar → Background → Scalar
effectiveAction bundle background =
  add bundle (gaussianDeterminant bundle background)
    (add bundle (interactionCumulant bundle background)
      (add bundle (constraintJacobian bundle background)
        (add bundle (gaugeFixingNormalization bundle background)
          (irrelevantRemainder bundle background))))

effectiveActionDecomposition :
  ∀ {Background Scalar}
  (bundle : FiniteEffectiveAction Background Scalar) →
  ∀ background →
  effectiveAction bundle background ≡
  add bundle (gaussianDeterminant bundle background)
    (add bundle (interactionCumulant bundle background)
      (add bundle (constraintJacobian bundle background)
        (add bundle (gaugeFixingNormalization bundle background)
          (irrelevantRemainder bundle background))))
effectiveActionDecomposition bundle background = refl
