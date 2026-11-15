module DASHI.Physics.YangMills.YMClayNativeSideFourC3VectorWeldExact where

------------------------------------------------------------------------
-- R443-C3: selected ORIGINAL side-four native SU(N)/SU(2) C3 in Vec form.
--
-- This is NOT an independently supplied "permutation invariant" action.
-- The spatial rotation is the exact existing CMP119 selected field C3:
-- (x0,x1,x2,x3) -> (x0,x3,x1,x2), with the matching 0,1,2,3
-- -> 0,2,3,1 axis permutation, and the original native side-four
-- forward-bond pullback of YMClayNativeRationalSU2Side4C3CarrierWeldExact.
--
-- The finite physical vector is the original 1024 positive-bond codec.
-- Proves exact vector C3 action, both inverses and third iterate = identity.
-- No new test field, action or full-function extensionality is supplied.
--
-- Unlike the generic --safe finite codec, this module imports existing
-- CMP119 C3 owners whose real analytic source chain is not audited safe.
-- Finite Haar/Fubini invariance still requires a concrete syntactic
-- LinkPermutation of adjacent swaps, or an independent finite general
-- bijection Fubini lemma. It is NOT inferred from mere bijectivity here.
--
-- Wilson/Balaban/previous DASHI native C3 theorem owners retain credit.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.Foundations.CMP119FlatSide4SpatialC3FieldCovarianceExact as C3
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayFiniteNativeBondReindexingSafeExact as Reindex

Bond : Set
Bond = Torus.PositiveBond Torus.four

forwardBond : Bond → Bond
forwardBond (Torus.pair site axis) =
  Torus.pair (C3.spatialC3Site site) (C3.spatialC3Axis axis)

backwardBond : Bond → Bond
backwardBond (Torus.pair site axis) =
  Torus.pair (C3.inverseSpatialC3Site site) (C3.inverseSpatialC3Axis axis)

axisForwardAfterBackward :
  ∀ axis → C3.spatialC3Axis (C3.inverseSpatialC3Axis axis) ≡ axis
axisForwardAfterBackward Hodge.axis0 = refl
axisForwardAfterBackward Hodge.axis1 = refl
axisForwardAfterBackward Hodge.axis2 = refl
axisForwardAfterBackward Hodge.axis3 = refl

forwardAfterBackward : ∀ bond → forwardBond (backwardBond bond) ≡ bond
forwardAfterBackward (Torus.pair site axis) =
  cong₂ Torus.pair
    (C3.spatialC3SiteAfterInverse site)
    (axisForwardAfterBackward axis)

backwardAfterForward : ∀ bond → backwardBond (forwardBond bond) ≡ bond
backwardAfterForward (Torus.pair site axis) =
  cong₂ Torus.pair
    (C3.inverseSpatialC3SiteAfter site)
    (C3.inverseSpatialC3AxisAfter axis)

siteOrderThree :
  ∀ site →
    C3.spatialC3Site (C3.spatialC3Site (C3.spatialC3Site site))
    ≡ site
siteOrderThree (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl

axisOrderThree :
  ∀ axis →
    C3.spatialC3Axis (C3.spatialC3Axis (C3.spatialC3Axis axis))
    ≡ axis
axisOrderThree Hodge.axis0 = refl
axisOrderThree Hodge.axis1 = refl
axisOrderThree Hodge.axis2 = refl
axisOrderThree Hodge.axis3 = refl

bondOrderThree :
  ∀ bond → forwardBond (forwardBond (forwardBond bond)) ≡ bond
bondOrderThree (Torus.pair site axis) =
  cong₂ Torus.pair
    (siteOrderThree site)
    (axisOrderThree axis)

module _ {Value : Set} where

  Vector : Set
  Vector = Vec.Vec Value (Codec.originalPositiveBondCount Torus.four)

  forwardVector : Vector → Vector
  forwardVector = Reindex.reindexBonds Torus.four forwardBond

  backwardVector : Vector → Vector
  backwardVector = Reindex.reindexBonds Torus.four backwardBond

  -- ACTUAL old native bond C3 (not a newly selected reindexing).
  nativeForwardIsVectorAt :
    ∀ vector bond →
    Codec.decodeOriginalBonds Torus.four (forwardVector vector) bond
    ≡
    Weld.nativeForwardC3Bonds
      (Codec.decodeOriginalBonds Torus.four vector) bond
  nativeForwardIsVectorAt vector (Torus.pair site axis) =
    Reindex.reindexAt Torus.four forwardBond vector
      (Torus.pair site axis)

  nativeForwardEncodesExactly :
    ∀ vector →
    Codec.encodeOriginalBonds Torus.four
      (Weld.nativeForwardC3Bonds
        (Codec.decodeOriginalBonds Torus.four vector))
    ≡ forwardVector vector
  nativeForwardEncodesExactly vector =
    Codec.originalBondsEncodePointwise Torus.four
      (Weld.nativeForwardC3Bonds
        (Codec.decodeOriginalBonds Torus.four vector))
      (λ bond →
        Codec.decodeOriginalBonds Torus.four vector (forwardBond bond))
      (λ where (Torus.pair site axis) → refl)

  forwardBackwardVector :
    ∀ vector → forwardVector (backwardVector vector) ≡ vector
  forwardBackwardVector vector =
    Reindex.reindexInverseLeft Torus.four
      forwardBond backwardBond vector backwardAfterForward

  backwardForwardVector :
    ∀ vector → backwardVector (forwardVector vector) ≡ vector
  backwardForwardVector vector =
    Reindex.reindexInverseRight Torus.four
      forwardBond backwardBond vector forwardAfterBackward

  forwardVectorOrderThree :
    ∀ vector →
      forwardVector (forwardVector (forwardVector vector)) ≡ vector
  forwardVectorOrderThree vector =
    Reindex.reindexOrderThree Torus.four
      forwardBond vector bondOrderThree
