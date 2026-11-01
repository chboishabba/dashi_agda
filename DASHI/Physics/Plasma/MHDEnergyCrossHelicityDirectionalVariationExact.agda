module DASHI.Physics.Plasma.MHDEnergyCrossHelicityDirectionalVariationExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field

------------------------------------------------------------------------
-- DIRECTIONAL VARIATION RECHART
--
-- For E = u^2+b^2 and Hc = u b, with tangent (Tu,Tb), define
--   dE  = 2 (u Tu + b Tb)
--   dHc = u Tb + b Tu.
-- If z+ = u+b, z- = u-b and T+ = Tu+Tb, T- = Tu-Tb, then
--
--   2 dE  = dE+ + dE-
--   4 dHc = dE+ - dE-
--
-- where dE+ = 2 z+ T+ and dE- = 2 z- T-.
------------------------------------------------------------------------

private
  sub : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

  two four : ∀ {r} {F : C3.RealField r} → C3.Carrier F
  two {F = F} = C3.add F (C3.one F) (C3.one F)
  four {F = F} = C3.add F two two

energyVariation :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
energyVariation {F = F} u b tu tb =
  C3.multiply F two
    (C3.add F (C3.multiply F u tu) (C3.multiply F b tb))

crossHelicityVariation :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
crossHelicityVariation {F = F} u b tu tb =
  C3.add F (C3.multiply F u tb) (C3.multiply F b tu)

plusVariation :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
plusVariation {F = F} u b tu tb =
  C3.multiply F two
    (C3.multiply F (C3.add F u b) (C3.add F tu tb))

minusVariation :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
minusVariation {F = F} u b tu tb =
  C3.multiply F two
    (C3.multiply F (sub u b) (sub tu tb))

energyVariationElsasserExact :
  ∀ {r} {F : C3.RealField r}
    (u b tu tb : C3.Carrier F) →
  C3.multiply F two (energyVariation u b tu tb)
  ≡ C3.add F (plusVariation u b tu tb) (minusVariation u b tu tb)
energyVariationElsasserExact {F = F} u b tu tb =
  R.solve 4
    (λ u b tu tb →
      ((R.Κ two R.⊗
          (R.Κ two R.⊗ ((u R.⊗ tu) R.⊕ (b R.⊗ tb))))
      R.⊜
      ((R.Κ two R.⊗ ((u R.⊕ b) R.⊗ (tu R.⊕ tb)))
        R.⊕
       (R.Κ two R.⊗
          ((u R.⊕ (R.⊝ b)) R.⊗ (tu R.⊕ (R.⊝ tb))))))
    refl u b tu tb
  where module R = Field.Solver F

crossHelicityVariationElsasserExact :
  ∀ {r} {F : C3.RealField r}
    (u b tu tb : C3.Carrier F) →
  C3.multiply F four (crossHelicityVariation u b tu tb)
  ≡ sub (plusVariation u b tu tb) (minusVariation u b tu tb)
crossHelicityVariationElsasserExact {F = F} u b tu tb =
  R.solve 4
    (λ u b tu tb →
      ((R.Κ four R.⊗ ((u R.⊗ tb) R.⊕ (b R.⊗ tu)))
      R.⊜
      ((R.Κ two R.⊗ ((u R.⊕ b) R.⊗ (tu R.⊕ tb)))
        R.⊕
       (R.⊝
         (R.Κ two R.⊗
           ((u R.⊕ (R.⊝ b)) R.⊗ (tu R.⊕ (R.⊝ tb)))))))
    refl u b tu tb
  where module R = Field.Solver F

record DirectionalVariationBoundary : Set where
  constructor directional-variation-boundary
  field
    plusMinusVariationCancellationCanFeedEnergyAndCrossHelicity : Bool
    plusMinusVariationCancellationCanFeedEnergyAndCrossHelicityIsTrue :
      plusMinusVariationCancellationCanFeedEnergyAndCrossHelicity ≡ true

    directionalRechartAloneProvesCyclicCancellation : Bool
    directionalRechartAloneProvesCyclicCancellationIsFalse :
      directionalRechartAloneProvesCyclicCancellation ≡ false

canonicalDirectionalVariationBoundary : DirectionalVariationBoundary
canonicalDirectionalVariationBoundary =
  directional-variation-boundary true refl false refl
