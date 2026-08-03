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

productNormMultiplicative : ∀ left right →
  SU2.squareℚ (productReal left right)
  + SU2.squareℚ (productI left right)
  + SU2.squareℚ (productJ left right)
  + SU2.squareℚ (productK left right)
  ≡ SU2.quaternionNormSq left * SU2.quaternionNormSq right
productNormMultiplicative left right =
  ℚRing.solve-∀
    (SU2.realPart left) (SU2.imagI left)
    (SU2.imagJ left) (SU2.imagK left)
    (SU2.realPart right) (SU2.imagI right)
    (SU2.imagJ right) (SU2.imagK right)

productUnitNorm : ∀ left right →
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
      (ℚRing.solve-∀))

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

inverseNormPreserved : ∀ value →
  SU2.squareℚ (SU2.realPart value)
  + SU2.squareℚ (negℚ (SU2.imagI value))
  + SU2.squareℚ (negℚ (SU2.imagJ value))
  + SU2.squareℚ (negℚ (SU2.imagK value))
  ≡ SU2.quaternionNormSq value
inverseNormPreserved value =
  ℚRing.solve-∀
    (SU2.realPart value) (SU2.imagI value)
    (SU2.imagJ value) (SU2.imagK value)

inverseUnitNorm : ∀ value →
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

multiplyAssociative : ∀ left middle right →
  multiplyRationalSU2 (multiplyRationalSU2 left middle) right
  ≡ multiplyRationalSU2 left (multiplyRationalSU2 middle right)
multiplyAssociative left middle right =
  rationalUnitQuaternionExtensionality
    (ℚRing.solve-∀
      (SU2.realPart left) (SU2.imagI left)
      (SU2.imagJ left) (SU2.imagK left)
      (SU2.realPart middle) (SU2.imagI middle)
      (SU2.imagJ middle) (SU2.imagK middle)
      (SU2.realPart right) (SU2.imagI right)
      (SU2.imagJ right) (SU2.imagK right))
    (ℚRing.solve-∀
      (SU2.realPart left) (SU2.imagI left)
      (SU2.imagJ left) (SU2.imagK left)
      (SU2.realPart middle) (SU2.imagI middle)
      (SU2.imagJ middle) (SU2.imagK middle)
      (SU2.realPart right) (SU2.imagI right)
      (SU2.imagJ right) (SU2.imagK right))
    (ℚRing.solve-∀
      (SU2.realPart left) (SU2.imagI left)
      (SU2.imagJ left) (SU2.imagK left)
      (SU2.realPart middle) (SU2.imagI middle)
      (SU2.imagJ middle) (SU2.imagK middle)
      (SU2.realPart right) (SU2.imagI right)
      (SU2.imagJ right) (SU2.imagK right))
    (ℚRing.solve-∀
      (SU2.realPart left) (SU2.imagI left)
      (SU2.imagJ left) (SU2.imagK left)
      (SU2.realPart middle) (SU2.imagI middle)
      (SU2.imagJ middle) (SU2.imagK middle)
      (SU2.realPart right) (SU2.imagI right)
      (SU2.imagJ right) (SU2.imagK right))

identityLeft : ∀ value →
  multiplyRationalSU2 identityRationalSU2 value ≡ value
identityLeft value = rationalUnitQuaternionExtensionality
  (ℚRing.solve-∀ (SU2.realPart value))
  (ℚRing.solve-∀ (SU2.imagI value))
  (ℚRing.solve-∀ (SU2.imagJ value))
  (ℚRing.solve-∀ (SU2.imagK value))

identityRight : ∀ value →
  multiplyRationalSU2 value identityRationalSU2 ≡ value
identityRight value = rationalUnitQuaternionExtensionality
  (ℚRing.solve-∀ (SU2.realPart value))
  (ℚRing.solve-∀ (SU2.imagI value))
  (ℚRing.solve-∀ (SU2.imagJ value))
  (ℚRing.solve-∀ (SU2.imagK value))

inverseLeft : ∀ value →
  multiplyRationalSU2 (inverseRationalSU2 value) value
  ≡ identityRationalSU2
inverseLeft value = rationalUnitQuaternionExtensionality
  (trans
    (ℚRing.solve-∀
      (SU2.realPart value) (SU2.imagI value)
      (SU2.imagJ value) (SU2.imagK value))
    (SU2.unitNormExact value))
  (ℚRing.solve-∀
    (SU2.realPart value) (SU2.imagI value)
    (SU2.imagJ value) (SU2.imagK value))
  (ℚRing.solve-∀
    (SU2.realPart value) (SU2.imagI value)
    (SU2.imagJ value) (SU2.imagK value))
  (ℚRing.solve-∀
    (SU2.realPart value) (SU2.imagI value)
    (SU2.imagJ value) (SU2.imagK value))

inverseRight : ∀ value →
  multiplyRationalSU2 value (inverseRationalSU2 value)
  ≡ identityRationalSU2
inverseRight value = rationalUnitQuaternionExtensionality
  (trans
    (ℚRing.solve-∀
      (SU2.realPart value) (SU2.imagI value)
      (SU2.imagJ value) (SU2.imagK value))
    (SU2.unitNormExact value))
  (ℚRing.solve-∀
    (SU2.realPart value) (SU2.imagI value)
    (SU2.imagJ value) (SU2.imagK value))
  (ℚRing.solve-∀
    (SU2.realPart value) (SU2.imagI value)
    (SU2.imagJ value) (SU2.imagK value))
  (ℚRing.solve-∀
    (SU2.realPart value) (SU2.imagI value)
    (SU2.imagJ value) (SU2.imagK value))

inverseProduct : ∀ left right →
  inverseRationalSU2 (multiplyRationalSU2 left right)
  ≡ multiplyRationalSU2
      (inverseRationalSU2 right)
      (inverseRationalSU2 left)
inverseProduct left right = rationalUnitQuaternionExtensionality
  (ℚRing.solve-∀
    (SU2.realPart left) (SU2.imagI left)
    (SU2.imagJ left) (SU2.imagK left)
    (SU2.realPart right) (SU2.imagI right)
    (SU2.imagJ right) (SU2.imagK right))
  (ℚRing.solve-∀
    (SU2.realPart left) (SU2.imagI left)
    (SU2.imagJ left) (SU2.imagK left)
    (SU2.realPart right) (SU2.imagI right)
    (SU2.imagJ right) (SU2.imagK right))
  (ℚRing.solve-∀
    (SU2.realPart left) (SU2.imagI left)
    (SU2.imagJ left) (SU2.imagK left)
    (SU2.realPart right) (SU2.imagI right)
    (SU2.imagJ right) (SU2.imagK right))
  (ℚRing.solve-∀
    (SU2.realPart left) (SU2.imagI left)
    (SU2.imagJ left) (SU2.imagK left)
    (SU2.realPart right) (SU2.imagI right)
    (SU2.imagJ right) (SU2.imagK right))

inverseInverse : ∀ value →
  inverseRationalSU2 (inverseRationalSU2 value) ≡ value
inverseInverse value = rationalUnitQuaternionExtensionality
  (ℚRing.solve-∀ (SU2.realPart value))
  (ℚRing.solve-∀ (SU2.imagI value))
  (ℚRing.solve-∀ (SU2.imagJ value))
  (ℚRing.solve-∀ (SU2.imagK value))

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
