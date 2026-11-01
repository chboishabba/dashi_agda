module DASHI.Physics.YangMills.BalabanSU2PolarizationWardIdentity where

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.BalabanFiniteOneStepCore using
  (FinitePolarizationData; polarization; divergence; scalarZero; wardLeft; wardRight)

polarizationWardLeft :
  ∀ {Background Direction Scalar : Set}
  (bundle : FinitePolarizationData Background Direction Scalar) →
  ∀ left right → polarization bundle (divergence bundle left) right ≡ scalarZero bundle
polarizationWardLeft = wardLeft

polarizationWardRight :
  ∀ {Background Direction Scalar : Set}
  (bundle : FinitePolarizationData Background Direction Scalar) →
  ∀ left right → polarization bundle left (divergence bundle right) ≡ scalarZero bundle
polarizationWardRight = wardRight
