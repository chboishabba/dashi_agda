module DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)
open import Relation.Binary.PropositionalEquality.WithK using (≡-irrelevant)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond

------------------------------------------------------------------------
-- Primary provenance.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Michael Creutz,
-- "Quarks, Gluons and Lattices", Cambridge University Press; originally
-- published 1983, open-access reissue 2022.
-- DOI: 10.1017/9781009290395.
--
-- The SU(2)-unit-quaternion identification is standard.  The component
-- identities and norm-one closure below are literal rational polynomial
-- proofs discharged by the standard-library rational ring solver.
------------------------------------------------------------------------

negℚ : ℚ → ℚ
negℚ value = 0ℚ - value

productReal productI productJ productK :
  SU2.RationalUnitQuaternion → SU2.RationalUnitQuaternion → ℚ
productReal left right =
  SU2.realPart left * SU2.realPart right
  - SU2.imagI left * SU2.imagI right
  - SU2.imagJ left * SU2.imagJ right
  - SU2.imagK left * SU2.imagK right
productI left right =
  SU2.realPart left * SU2.imagI right
  + SU2.imagI left * SU2.realPart right
  + SU2.imagJ left * SU2.imagK right
  - SU2.imagK left * SU2.imagJ right
productJ left right =
  SU2.realPart left * SU2.imagJ right
  - SU2.imagI left * SU2.imagK right
  + SU2.imagJ left * SU2.realPart right
  + SU2.imagK left * SU2.imagI right
productK left right =
  SU2.realPart left * SU2.imagK right
  + SU2.imagI left * SU2.imagJ right
  - SU2.imagJ left * SU2.imagI right
  + SU2.imagK left * SU2.realPart right

productNormMultiplicative : ∀ (left right : SU2.RationalUnitQuaternion) →
  SU2.squareℚ (productReal left right)
  + SU2.squareℚ (productI left right)
  + SU2.squareℚ (productJ left right)
  + SU2.squareℚ (productK left right)
  ≡ SU2.quaternionNormSq left * SU2.quaternionNormSq right
productNormMultiplicative left right =
  regroup
    (SU2.realPart left) (SU2.imagI left) (SU2.imagJ left) (SU2.imagK left)
    (SU2.realPart right) (SU2.imagI right) (SU2.imagJ right) (SU2.imagK right)
  where
  regroup : (w1 x1 y1 z1 w2 x2 y2 z2 : ℚ) →
    SU2.squareℚ (w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2)
    + SU2.squareℚ (w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2)
    + SU2.squareℚ (w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2)
    + SU2.squareℚ (w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2)
    ≡ (w1 * w1 + x1 * x1 + y1 * y1 + z1 * z1) * (w2 * w2 + x2 * x2 + y2 * y2 + z2 * z2)
  regroup = ℚRing.solve-∀

productUnitNorm : ∀ (left right : SU2.RationalUnitQuaternion) →
  SU2.squareℚ (productReal left right)
  + SU2.squareℚ (productI left right)
  + SU2.squareℚ (productJ left right)
  + SU2.squareℚ (productK left right)
  ≡ 1ℚ
productUnitNorm left right =
  trans
    (productNormMultiplicative left right)
    (trans
      (cong₂ _*_
        (SU2.unitNormExact left)
        (SU2.unitNormExact right))
      (regroup))
  where
  regroup : 1ℚ * 1ℚ ≡ 1ℚ
  regroup = ℚRing.solve-∀

multiplyRationalSU2 :
  SU2.RationalUnitQuaternion →
  SU2.RationalUnitQuaternion →
  SU2.RationalUnitQuaternion
multiplyRationalSU2 left right = SU2.rationalUnitQuaternion
  (productReal left right)
  (productI left right)
  (productJ left right)
  (productK left right)
  (productUnitNorm left right)

inverseNormPreserved : ∀ (value : SU2.RationalUnitQuaternion) →
  SU2.squareℚ (SU2.realPart value)
  + SU2.squareℚ (negℚ (SU2.imagI value))
  + SU2.squareℚ (negℚ (SU2.imagJ value))
  + SU2.squareℚ (negℚ (SU2.imagK value))
  ≡ SU2.quaternionNormSq value
inverseNormPreserved value =
  regroup
    (SU2.realPart value) (SU2.imagI value) (SU2.imagJ value) (SU2.imagK value)
  where
  regroup : (w x y zVal : ℚ) →
    SU2.squareℚ w
    + SU2.squareℚ (negℚ x)
    + SU2.squareℚ (negℚ y)
    + SU2.squareℚ (negℚ zVal)
    ≡ w * w + x * x + y * y + zVal * zVal
  regroup = ℚRing.solve-∀

inverseUnitNorm : ∀ (value : SU2.RationalUnitQuaternion) →
  SU2.squareℚ (SU2.realPart value)
  + SU2.squareℚ (negℚ (SU2.imagI value))
  + SU2.squareℚ (negℚ (SU2.imagJ value))
  + SU2.squareℚ (negℚ (SU2.imagK value))
  ≡ 1ℚ
inverseUnitNorm value =
  trans (inverseNormPreserved value) (SU2.unitNormExact value)

inverseRationalSU2 :
  SU2.RationalUnitQuaternion → SU2.RationalUnitQuaternion
inverseRationalSU2 value = SU2.rationalUnitQuaternion
  (SU2.realPart value)
  (negℚ (SU2.imagI value))
  (negℚ (SU2.imagJ value))
  (negℚ (SU2.imagK value))
  (inverseUnitNorm value)

identityRationalSU2 : SU2.RationalUnitQuaternion
identityRationalSU2 = SU2.rationalUnitQuaternion
  1ℚ 0ℚ 0ℚ 0ℚ (ℚRing.solve-∀)

rationalUnitQuaternionExtensionality :
  ∀ {left right : SU2.RationalUnitQuaternion} →
  SU2.realPart left ≡ SU2.realPart right →
  SU2.imagI left ≡ SU2.imagI right →
  SU2.imagJ left ≡ SU2.imagJ right →
  SU2.imagK left ≡ SU2.imagK right →
  left ≡ right
rationalUnitQuaternionExtensionality
  {SU2.rationalUnitQuaternion a b c d normLeft}
  {SU2.rationalUnitQuaternion .a .b .c .d normRight}
  refl refl refl refl =
  cong (SU2.rationalUnitQuaternion a b c d)
    (≡-irrelevant normLeft normRight)

multiplyAssociative : ∀ (left middle right : SU2.RationalUnitQuaternion) →
  multiplyRationalSU2 (multiplyRationalSU2 left middle) right
  ≡ multiplyRationalSU2 left (multiplyRationalSU2 middle right)
multiplyAssociative left middle right =
  rationalUnitQuaternionExtensionality
    (regroup1
      (SU2.realPart left) (SU2.imagI left) (SU2.imagJ left) (SU2.imagK left)
      (SU2.realPart middle) (SU2.imagI middle) (SU2.imagJ middle) (SU2.imagK middle)
      (SU2.realPart right) (SU2.imagI right) (SU2.imagJ right) (SU2.imagK right))
    (regroup2
      (SU2.realPart left) (SU2.imagI left) (SU2.imagJ left) (SU2.imagK left)
      (SU2.realPart middle) (SU2.imagI middle) (SU2.imagJ middle) (SU2.imagK middle)
      (SU2.realPart right) (SU2.imagI right) (SU2.imagJ right) (SU2.imagK right))
    (regroup3
      (SU2.realPart left) (SU2.imagI left) (SU2.imagJ left) (SU2.imagK left)
      (SU2.realPart middle) (SU2.imagI middle) (SU2.imagJ middle) (SU2.imagK middle)
      (SU2.realPart right) (SU2.imagI right) (SU2.imagJ right) (SU2.imagK right))
    (regroup4
      (SU2.realPart left) (SU2.imagI left) (SU2.imagJ left) (SU2.imagK left)
      (SU2.realPart middle) (SU2.imagI middle) (SU2.imagJ middle) (SU2.imagK middle)
      (SU2.realPart right) (SU2.imagI right) (SU2.imagJ right) (SU2.imagK right))
  where
  regroup1 : (w1 x1 y1 z1 w2 x2 y2 z2 w3 x3 y3 z3 : ℚ) →
    (w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2) * w3
    - (w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2) * x3
    - (w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2) * y3
    - (w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2) * z3
    ≡ w1 * (w2 * w3 - x2 * x3 - y2 * y3 - z2 * z3)
    - x1 * (w2 * x3 + x2 * w3 + y2 * z3 - z2 * y3)
    - y1 * (w2 * y3 - x2 * z3 + y2 * w3 + z2 * x3)
    - z1 * (w2 * z3 + x2 * y3 - y2 * x3 + z2 * w3)
  regroup1 = ℚRing.solve-∀

  regroup2 : (w1 x1 y1 z1 w2 x2 y2 z2 w3 x3 y3 z3 : ℚ) →
    (w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2) * x3
    + (w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2) * w3
    + (w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2) * z3
    - (w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2) * y3
    ≡ w1 * (w2 * x3 + x2 * w3 + y2 * z3 - z2 * y3)
    + x1 * (w2 * w3 - x2 * x3 - y2 * y3 - z2 * z3)
    + y1 * (w2 * z3 + x2 * y3 - y2 * x3 + z2 * w3)
    - z1 * (w2 * y3 - x2 * z3 + y2 * w3 + z2 * x3)
  regroup2 = ℚRing.solve-∀

  regroup3 : (w1 x1 y1 z1 w2 x2 y2 z2 w3 x3 y3 z3 : ℚ) →
    (w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2) * y3
    - (w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2) * z3
    + (w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2) * w3
    + (w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2) * x3
    ≡ w1 * (w2 * y3 - x2 * z3 + y2 * w3 + z2 * x3)
    - x1 * (w2 * z3 + x2 * y3 - y2 * x3 + z2 * w3)
    + y1 * (w2 * w3 - x2 * x3 - y2 * y3 - z2 * z3)
    + z1 * (w2 * x3 + x2 * w3 + y2 * z3 - z2 * y3)
  regroup3 = ℚRing.solve-∀

  regroup4 : (w1 x1 y1 z1 w2 x2 y2 z2 w3 x3 y3 z3 : ℚ) →
    (w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2) * z3
    + (w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2) * y3
    - (w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2) * x3
    + (w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2) * w3
    ≡ w1 * (w2 * z3 + x2 * y3 - y2 * x3 + z2 * w3)
    + x1 * (w2 * y3 - x2 * z3 + y2 * w3 + z2 * x3)
    - y1 * (w2 * x3 + x2 * w3 + y2 * z3 - z2 * y3)
    + z1 * (w2 * w3 - x2 * x3 - y2 * y3 - z2 * z3)
  regroup4 = ℚRing.solve-∀

identityLeft : ∀ (value : SU2.RationalUnitQuaternion) →
  multiplyRationalSU2 identityRationalSU2 value ≡ value
identityLeft value = rationalUnitQuaternionExtensionality
  (regroup (SU2.realPart value))
  (regroup (SU2.imagI value))
  (regroup (SU2.imagJ value))
  (regroup (SU2.imagK value))
  where
  regroup : (v : ℚ) → 1ℚ * v ≡ v
  regroup = ℚRing.solve-∀

identityRight : ∀ (value : SU2.RationalUnitQuaternion) →
  multiplyRationalSU2 value identityRationalSU2 ≡ value
identityRight value = rationalUnitQuaternionExtensionality
  (regroup (SU2.realPart value))
  (regroup (SU2.imagI value))
  (regroup (SU2.imagJ value))
  (regroup (SU2.imagK value))
  where
  regroup : (v : ℚ) → v * 1ℚ ≡ v
  regroup = ℚRing.solve-∀

inverseLeft : ∀ (value : SU2.RationalUnitQuaternion) →
  multiplyRationalSU2 (inverseRationalSU2 value) value
  ≡ identityRationalSU2
inverseLeft value = rationalUnitQuaternionExtensionality
  (trans
    (regroup1
      (SU2.realPart value) (SU2.imagI value)
      (SU2.imagJ value) (SU2.imagK value))
    (SU2.unitNormExact value))
  (regroup2
    (SU2.realPart value) (SU2.imagI value)
    (SU2.imagJ value) (SU2.imagK value))
  (regroup3
    (SU2.realPart value) (SU2.imagI value)
    (SU2.imagJ value) (SU2.imagK value))
  (regroup4
    (SU2.realPart value) (SU2.imagI value)
    (SU2.imagJ value) (SU2.imagK value))
  where
  regroup1 : (w x y zVal : ℚ) → w * w - (negℚ x) * x - (negℚ y) * y - (negℚ zVal) * zVal ≡ w * w + x * x + y * y + zVal * zVal
  regroup1 = ℚRing.solve-∀
  regroup2 : (w x y zVal : ℚ) → w * x + (negℚ x) * w + (negℚ y) * zVal - (negℚ zVal) * y ≡ 0ℚ
  regroup2 = ℚRing.solve-∀
  regroup3 : (w x y zVal : ℚ) → w * y - (negℚ x) * zVal + (negℚ y) * w + (negℚ zVal) * x ≡ 0ℚ
  regroup3 = ℚRing.solve-∀
  regroup4 : (w x y zVal : ℚ) → w * zVal + (negℚ x) * y - (negℚ y) * x + (negℚ zVal) * w ≡ 0ℚ
  regroup4 = ℚRing.solve-∀

inverseRight : ∀ (value : SU2.RationalUnitQuaternion) →
  multiplyRationalSU2 value (inverseRationalSU2 value)
  ≡ identityRationalSU2
inverseRight value = rationalUnitQuaternionExtensionality
  (trans
    (regroup1
      (SU2.realPart value) (SU2.imagI value)
      (SU2.imagJ value) (SU2.imagK value))
    (SU2.unitNormExact value))
  (regroup2
    (SU2.realPart value) (SU2.imagI value)
    (SU2.imagJ value) (SU2.imagK value))
  (regroup3
    (SU2.realPart value) (SU2.imagI value)
    (SU2.imagJ value) (SU2.imagK value))
  (regroup4
    (SU2.realPart value) (SU2.imagI value)
    (SU2.imagJ value) (SU2.imagK value))
  where
  regroup1 : (w x y zVal : ℚ) → w * w - x * (negℚ x) - y * (negℚ y) - zVal * (negℚ zVal) ≡ w * w + x * x + y * y + zVal * zVal
  regroup1 = ℚRing.solve-∀
  regroup2 : (w x y zVal : ℚ) → w * (negℚ x) + x * w + y * (negℚ zVal) - zVal * (negℚ y) ≡ 0ℚ
  regroup2 = ℚRing.solve-∀
  regroup3 : (w x y zVal : ℚ) → w * (negℚ y) - x * (negℚ zVal) + y * w + zVal * (negℚ x) ≡ 0ℚ
  regroup3 = ℚRing.solve-∀
  regroup4 : (w x y zVal : ℚ) → w * (negℚ zVal) + x * (negℚ y) - y * (negℚ x) + zVal * w ≡ 0ℚ
  regroup4 = ℚRing.solve-∀

inverseProduct : ∀ (left right : SU2.RationalUnitQuaternion) →
  inverseRationalSU2 (multiplyRationalSU2 left right)
  ≡ multiplyRationalSU2
      (inverseRationalSU2 right)
      (inverseRationalSU2 left)
inverseProduct left right = rationalUnitQuaternionExtensionality
  (regroup1
    (SU2.realPart left) (SU2.imagI left) (SU2.imagJ left) (SU2.imagK left)
    (SU2.realPart right) (SU2.imagI right) (SU2.imagJ right) (SU2.imagK right))
  (regroup2
    (SU2.realPart left) (SU2.imagI left) (SU2.imagJ left) (SU2.imagK left)
    (SU2.realPart right) (SU2.imagI right) (SU2.imagJ right) (SU2.imagK right))
  (regroup3
    (SU2.realPart left) (SU2.imagI left) (SU2.imagJ left) (SU2.imagK left)
    (SU2.realPart right) (SU2.imagI right) (SU2.imagJ right) (SU2.imagK right))
  (regroup4
    (SU2.realPart left) (SU2.imagI left) (SU2.imagJ left) (SU2.imagK left)
    (SU2.realPart right) (SU2.imagI right) (SU2.imagJ right) (SU2.imagK right))
  where
  regroup1 : (w1 x1 y1 z1 w2 x2 y2 z2 : ℚ) →
    w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2
    ≡ w2 * w1 - (negℚ x2) * (negℚ x1) - (negℚ y2) * (negℚ y1) - (negℚ z2) * (negℚ z1)
  regroup1 = ℚRing.solve-∀

  regroup2 : (w1 x1 y1 z1 w2 x2 y2 z2 : ℚ) →
    negℚ (w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2)
    ≡ w2 * (negℚ x1) + (negℚ x2) * w1 + (negℚ y2) * (negℚ z1) - (negℚ z2) * (negℚ y1)
  regroup2 = ℚRing.solve-∀

  regroup3 : (w1 x1 y1 z1 w2 x2 y2 z2 : ℚ) →
    negℚ (w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2)
    ≡ w2 * (negℚ y1) - (negℚ x2) * (negℚ z1) + (negℚ y2) * w1 + (negℚ z2) * (negℚ x1)
  regroup3 = ℚRing.solve-∀

  regroup4 : (w1 x1 y1 z1 w2 x2 y2 z2 : ℚ) →
    negℚ (w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2)
    ≡ w2 * (negℚ z1) + (negℚ x2) * (negℚ y1) - (negℚ y2) * (negℚ x1) + (negℚ z2) * w1
  regroup4 = ℚRing.solve-∀

inverseInverse : ∀ (value : SU2.RationalUnitQuaternion) →
  inverseRationalSU2 (inverseRationalSU2 value) ≡ value
inverseInverse value = rationalUnitQuaternionExtensionality
  refl
  (regroup (SU2.imagI value))
  (regroup (SU2.imagJ value))
  (regroup (SU2.imagK value))
  where
  regroup : (x : ℚ) → negℚ (negℚ x) ≡ x
  regroup = ℚRing.solve-∀

rationalSU2ExactLinkGroup :
  Bond.ExactLinkGroup SU2.RationalUnitQuaternion
rationalSU2ExactLinkGroup = record
  { identity = identityRationalSU2
  ; multiply = multiplyRationalSU2
  ; inverse = inverseRationalSU2
  ; multiplyAssociative = multiplyAssociative
  ; identityLeft = identityLeft
  ; identityRight = identityRight
  ; inverseLeft = inverseLeft
  ; inverseRight = inverseRight
  ; inverseProduct = inverseProduct
  ; inverseInverse = inverseInverse
  }

rationalQuaternionCoordinateAlgebraLevel : ProofLevel
rationalQuaternionCoordinateAlgebraLevel = machineChecked

rationalQuaternionUnitNormClosureLevel : ProofLevel
rationalQuaternionUnitNormClosureLevel = machineChecked

rationalSU2ExactGroupLawLevel : ProofLevel
rationalSU2ExactGroupLawLevel = machineChecked
