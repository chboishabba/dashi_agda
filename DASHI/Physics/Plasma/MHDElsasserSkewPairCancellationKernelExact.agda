module DASHI.Physics.Plasma.MHDElsasserSkewPairCancellationKernelExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field

------------------------------------------------------------------------
-- GENERIC SKEW-PAIR CANCELLATION KERNEL
--
-- MHD Elsasser couplings admit a source-backed antisymmetry under exchange of
-- paired slots.  This module owns only the application-neutral algebra:
--
--   A xy + (-A) yx = 0.
--
-- The literal MHD application must still prove that its two mode-transfer
-- channels really are this same pair before this theorem may be consumed.
------------------------------------------------------------------------

pairTransfer :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
pairTransfer {F = F} a x y = C3.multiply F a (C3.multiply F x y)

skewPairTransfer :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
skewPairTransfer {F = F} a x y =
  C3.multiply F (C3.negate F a) (C3.multiply F y x)

skewPairCancelsExact :
  ∀ {r} {F : C3.RealField r}
    (a x y : C3.Carrier F) →
  C3.add F (pairTransfer a x y) (skewPairTransfer a x y)
  ≡ C3.zero F
skewPairCancelsExact {F = F} a x y =
  R.solve 3
    (λ a x y →
      ((a R.⊗ (x R.⊗ y))
        R.⊕ ((R.⊝ a) R.⊗ (y R.⊗ x)))
      R.⊜ R.Κ (C3.zero F))
    refl a x y
  where module R = Field.Solver F

record SkewPairBoundary : Set where
  constructor skew-pair-boundary
  field
    skewPairKernelIsSpecificToNavierStokes : Bool
    skewPairKernelIsSpecificToNavierStokesIsFalse :
      skewPairKernelIsSpecificToNavierStokes ≡ false

    abstractSkewPairProvesLiteralMHDPairing : Bool
    abstractSkewPairProvesLiteralMHDPairingIsFalse :
      abstractSkewPairProvesLiteralMHDPairing ≡ false

    cancellationOccursBeforeAbsoluteValue : Bool
    cancellationOccursBeforeAbsoluteValueIsTrue :
      cancellationOccursBeforeAbsoluteValue ≡ true

canonicalSkewPairBoundary : SkewPairBoundary
canonicalSkewPairBoundary =
  skew-pair-boundary false refl false refl true refl
