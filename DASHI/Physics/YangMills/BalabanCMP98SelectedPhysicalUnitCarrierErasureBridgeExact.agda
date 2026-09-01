{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98SelectedPhysicalUnitCarrierErasureBridgeExact where

------------------------------------------------------------------------
-- BIDI REPRESENTATION BRIDGE: EXACT UNIT-QUATERNION PATH ALGEBRA -> RAW
-- QUATERNION COORDINATES USED BY THE SELECTED PRINCIPAL CHART
--
-- Round187 constructs the canonical selected physical realization on the
-- repository's exact `RationalUnitQuaternion` group carrier.  The older
-- physical principal chart is expressed on raw rational-quaternion coordinates.
-- This file proves that erasure preserves the exact group word, so no parallel
-- raw-quaternion group structure is required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (-_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Group
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionCoreExact as Q
import DASHI.Physics.YangMills.BalabanCMP109QuaternionPathTransportTelescopeExact as RawPath
import DASHI.Physics.YangMills.BalabanCMP98SelectedPhysicalUnitCarrierRound187Exact as R187

eraseIdentity :
  R187.eraseUnitQuaternion Group.identityRationalSU2 ≡ Q.oneQ
eraseIdentity = refl

eraseMultiply : ∀ left right →
  R187.eraseUnitQuaternion (Group.multiplyRationalSU2 left right)
  ≡ Q._*q_
      (R187.eraseUnitQuaternion left)
      (R187.eraseUnitQuaternion right)
eraseMultiply left right = refl

eraseInverse : ∀ value →
  R187.eraseUnitQuaternion (Group.inverseRationalSU2 value)
  ≡ Q.quat
      (Q.q0 (R187.eraseUnitQuaternion value))
      (- Q.q1 (R187.eraseUnitQuaternion value))
      (- Q.q2 (R187.eraseUnitQuaternion value))
      (- Q.q3 (R187.eraseUnitQuaternion value))
eraseInverse value = refl

eraseList : List SU2.RationalUnitQuaternion → List Q.RationalQuaternion
eraseList [] = []
eraseList (value ∷ values) =
  R187.eraseUnitQuaternion value ∷ eraseList values

productUnit : List SU2.RationalUnitQuaternion → SU2.RationalUnitQuaternion
productUnit [] = Group.identityRationalSU2
productUnit (value ∷ values) =
  Group.multiplyRationalSU2 value (productUnit values)

eraseProductList : ∀ values →
  R187.eraseUnitQuaternion (productUnit values)
  ≡ RawPath.pathProduct (eraseList values)
eraseProductList [] = eraseIdentity
eraseProductList (value ∷ values) =
  trans
    (eraseMultiply value (productUnit values))
    (cong
      (Q._*q_ (R187.eraseUnitQuaternion value))
      (eraseProductList values))

-- Pointwise erasure of the repository oriented-link convention.  Positive
-- traversal is direct erasure; negative traversal is erasure of the exact
-- unit-quaternion inverse and therefore raw quaternion conjugation coordinates.
eraseOrientedLinkPositive :
  ∀ {n}
    (realization : Bond.PeriodicBondGaugeRealization
      n SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup)
    site axis →
  R187.eraseUnitQuaternion
    (Bond.orientedLink realization site (pair axis true))
  ≡ R187.eraseUnitQuaternion
      (Bond.bondField realization (pair site axis))
eraseOrientedLinkPositive realization site axis = refl

eraseOrientedLinkNegative :
  ∀ {n}
    (realization : Bond.PeriodicBondGaugeRealization
      n SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup)
    site axis →
  R187.eraseUnitQuaternion
    (Bond.orientedLink realization site (pair axis false))
  ≡ Q.quat
      (Q.q0 (R187.eraseUnitQuaternion
        (Bond.bondField realization
          (pair (Bond.negativeStep site axis) axis))))
      (- Q.q1 (R187.eraseUnitQuaternion
        (Bond.bondField realization
          (pair (Bond.negativeStep site axis) axis))))
      (- Q.q2 (R187.eraseUnitQuaternion
        (Bond.bondField realization
          (pair (Bond.negativeStep site axis) axis))))
      (- Q.q3 (R187.eraseUnitQuaternion
        (Bond.bondField realization
          (pair (Bond.negativeStep site axis) axis))))
eraseOrientedLinkNegative realization site axis =
  eraseInverse
    (Bond.bondField realization
      (pair (Bond.negativeStep site axis) axis))

rawPathFactors :
  ∀ {n}
    (realization : Bond.PeriodicBondGaugeRealization
      n SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup) →
  Periodic.PeriodicBlock n → List Word.SignedAxis4 →
  List Q.RationalQuaternion
rawPathFactors realization site [] = []
rawPathFactors realization site (direction ∷ directions) =
  R187.eraseUnitQuaternion (Bond.orientedLink realization site direction)
  ∷ rawPathFactors realization (Bond.walkStep site direction) directions

-- Exact path recursion in raw coordinates.  This is the representation theorem
-- needed by the selected raw principal chart: erasing the typed path holonomy
-- is the same ordered raw quaternion product of erased oriented factors.
erasedPathHolonomyIsRawPathProduct :
  ∀ {n}
    (realization : Bond.PeriodicBondGaugeRealization
      n SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup)
    site directions →
  R187.eraseUnitQuaternion
    (Bond.pathHolonomy realization site directions)
  ≡ RawPath.pathProduct (rawPathFactors realization site directions)
erasedPathHolonomyIsRawPathProduct realization site [] = eraseIdentity
erasedPathHolonomyIsRawPathProduct realization site (direction ∷ directions) =
  trans
    (eraseMultiply
      (Bond.orientedLink realization site direction)
      (Bond.pathHolonomy realization
        (Bond.walkStep site direction) directions))
    (cong
      (Q._*q_
        (R187.eraseUnitQuaternion
          (Bond.orientedLink realization site direction)))
      (erasedPathHolonomyIsRawPathProduct realization
        (Bond.walkStep site direction) directions))

cmp98SelectedPhysicalUnitCarrierErasureHomomorphismLevel : ProofLevel
cmp98SelectedPhysicalUnitCarrierErasureHomomorphismLevel = machineChecked

cmp98SelectedPhysicalPathErasureLevel : ProofLevel
cmp98SelectedPhysicalPathErasureLevel = machineChecked
