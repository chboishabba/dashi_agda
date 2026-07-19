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
effectiveAction data background =
  add data (gaussianDeterminant data background)
    (add data (interactionCumulant data background)
      (add data (constraintJacobian data background)
        (add data (gaugeFixingNormalization data background)
          (irrelevantRemainder data background))))

effectiveActionDecomposition :
  ∀ {Background Scalar}
  (data : FiniteEffectiveAction Background Scalar) →
  ∀ background →
  effectiveAction data background ≡
  add data (gaussianDeterminant data background)
    (add data (interactionCumulant data background)
      (add data (constraintJacobian data background)
        (add data (gaugeFixingNormalization data background)
          (irrelevantRemainder data background))))
effectiveActionDecomposition data background = refl
