module DASHI.Physics.Plasma.ElsasserAmplitudeRechartAlgebraExact where

------------------------------------------------------------------------
-- EXACT ELSASSER AMPLITUDE RECHART ALGEBRA
--
-- Work division-free.  For each Fourier/helical slot x,
--
--   z+_x = u_x + b_x
--   z-_x = u_x - b_x.
--
-- Then for two ordered slots p,q:
--
--   2 (u_p u_q - b_p b_q)
--     = z+_p z-_q + z-_p z+_q
--
--   2 (u_p b_q - b_p u_q)
--     = z-_p z+_q - z+_p z-_q.
--
-- Hence same-Elsasser products cancel algebraically before any PDE estimate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field

private
  sub : ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

  two : ∀ {r} {F : C3.RealField r} → C3.Carrier F
  two {F = F} = C3.add F (C3.one F) (C3.one F)

zPlus : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F → C3.Carrier F
zPlus {F = F} u b = C3.add F u b

zMinus : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F → C3.Carrier F
zMinus {F = F} u b = sub u b

momentumAmplitude : ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
momentumAmplitude {F = F} up bp uq bq =
  sub (C3.multiply F up uq) (C3.multiply F bp bq)

inductionAmplitude : ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
inductionAmplitude {F = F} up bp uq bq =
  sub (C3.multiply F up bq) (C3.multiply F bp uq)

plusMinusProduct : ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
plusMinusProduct {F = F} up bp uq bq =
  C3.multiply F (zPlus up bp) (zMinus uq bq)

minusPlusProduct : ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
minusPlusProduct {F = F} up bp uq bq =
  C3.multiply F (zMinus up bp) (zPlus uq bq)

momentumAmplitudeElsasserExact :
  ∀ {r} {F : C3.RealField r}
    (up bp uq bq : C3.Carrier F) →
  C3.multiply F two (momentumAmplitude up bp uq bq)
  ≡ C3.add F
      (plusMinusProduct up bp uq bq)
      (minusPlusProduct up bp uq bq)
momentumAmplitudeElsasserExact {F = F} up bp uq bq =
  R.solve 4
    (λ up bp uq bq →
      (((R.Κ (C3.one F) R.⊕ R.Κ (C3.one F))
        R.⊗ ((up R.⊗ uq) R.⊕ (R.⊝ (bp R.⊗ bq))))
      R.⊜
      (((up R.⊕ bp) R.⊗ (uq R.⊕ (R.⊝ bq)))
        R.⊕ ((up R.⊕ (R.⊝ bp)) R.⊗ (uq R.⊕ bq))))
    refl up bp uq bq
  where module R = Field.Solver F

inductionAmplitudeElsasserExact :
  ∀ {r} {F : C3.RealField r}
    (up bp uq bq : C3.Carrier F) →
  C3.multiply F two (inductionAmplitude up bp uq bq)
  ≡ sub
      (minusPlusProduct up bp uq bq)
      (plusMinusProduct up bp uq bq)
inductionAmplitudeElsasserExact {F = F} up bp uq bq =
  R.solve 4
    (λ up bp uq bq →
      (((R.Κ (C3.one F) R.⊕ R.Κ (C3.one F))
        R.⊗ ((up R.⊗ bq) R.⊕ (R.⊝ (bp R.⊗ uq))))
      R.⊜
      (((up R.⊕ (R.⊝ bp)) R.⊗ (uq R.⊕ bq))
        R.⊕
        (R.⊝ ((up R.⊕ bp) R.⊗ (uq R.⊕ (R.⊝ bq))))))
    refl up bp uq bq
  where module R = Field.Solver F

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record ElsasserAmplitudeBoundary : Set where
  constructor elsasser-amplitude-boundary
  field
    momentumContainsSameSignElsasserProductAfterExpansion : Bool
    momentumContainsSameSignElsasserProductAfterExpansionIsFalse :
      momentumContainsSameSignElsasserProductAfterExpansion ≡ false

    inductionContainsSameSignElsasserProductAfterExpansion : Bool
    inductionContainsSameSignElsasserProductAfterExpansionIsFalse :
      inductionContainsSameSignElsasserProductAfterExpansion ≡ false

    momentumMixedProductsAreSymmetricCombination : Bool
    momentumMixedProductsAreSymmetricCombinationIsTrue :
      momentumMixedProductsAreSymmetricCombination ≡ true

    inductionMixedProductsAreAntisymmetricCombination : Bool
    inductionMixedProductsAreAntisymmetricCombinationIsTrue :
      inductionMixedProductsAreAntisymmetricCombination ≡ true

canonicalElsasserAmplitudeBoundary : ElsasserAmplitudeBoundary
canonicalElsasserAmplitudeBoundary =
  elsasser-amplitude-boundary false refl false refl true refl true refl
