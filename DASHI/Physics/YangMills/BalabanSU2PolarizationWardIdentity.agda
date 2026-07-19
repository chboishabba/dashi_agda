module DASHI.Physics.YangMills.BalabanSU2PolarizationWardIdentity where

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.BalabanFiniteOneStepCore using
  (FinitePolarizationData; polarization; divergence; scalarZero; wardLeft; wardRight)

polarizationWardLeft :
  ∀ {Background Direction Scalar}
  (data : FinitePolarizationData Background Direction Scalar) →
  ∀ left right → polarization data (divergence data left) right ≡ scalarZero data
polarizationWardLeft = wardLeft

polarizationWardRight :
  ∀ {Background Direction Scalar}
  (data : FinitePolarizationData Background Direction Scalar) →
  ∀ left right → polarization data left (divergence data right) ≡ scalarZero data
polarizationWardRight = wardRight
