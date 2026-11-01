{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98RawUnitPathHomomorphismRound189Exact where

------------------------------------------------------------------------
-- ROUND189 A1 BIDI: THE UNIT-QUATERNION PERIODIC REALIZATION AND THE RAW
-- RATIONAL-QUATERNION WILSON CARRIER HAVE THE SAME MULTIPLICATIVE PATH DATA
-- AFTER FORGETTING ONLY THE UNIT-NORM WITNESS.
--
-- R187 constructed the selected physical background directly on the exact
-- RationalUnitQuaternion periodic carrier.  This file proves the remaining
-- representation seam rather than postulating a second raw-quaternion group:
-- erasure preserves identity, multiplication, inverse and therefore arbitrary
-- path holonomy.  The raw side is only the quaternion product fold actually
-- consumed by the Wilson/variational representation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact using
  (SignedAxis4)
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionCoreExact as Q
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Group
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanCMP98SelectedPhysicalUnitCarrierRound187Exact as R187

eraseIdentity :
  R187.eraseUnitQuaternion Group.identityRationalSU2 ≡ Q.oneQ
eraseIdentity = refl

eraseMultiply : ∀ left right →
  R187.eraseUnitQuaternion (Group.multiplyRationalSU2 left right)
  ≡
  R187.eraseUnitQuaternion left Q.*q R187.eraseUnitQuaternion right
eraseMultiply left right = refl

rawInverse : SU2.RationalUnitQuaternion → Q.RationalQuaternion
rawInverse value =
  Q.quat
    (SU2.realPart value)
    (Group.negℚ (SU2.imagI value))
    (Group.negℚ (SU2.imagJ value))
    (Group.negℚ (SU2.imagK value))

eraseInverse : ∀ value →
  R187.eraseUnitQuaternion (Group.inverseRationalSU2 value)
  ≡ rawInverse value
eraseInverse value = refl

rawPathHolonomy :
  ∀ {n}
    (realization : Bond.PeriodicBondGaugeRealization
      n SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup) →
    Periodic.PeriodicBlock n →
    List SignedAxis4 →
    Q.RationalQuaternion
rawPathHolonomy realization site [] = Q.oneQ
rawPathHolonomy realization site (direction ∷ directions) =
  R187.eraseUnitQuaternion (Bond.orientedLink realization site direction)
  Q.*q
  rawPathHolonomy realization (Bond.walkStep site direction) directions

erasePathHolonomy :
  ∀ {n}
    (realization : Bond.PeriodicBondGaugeRealization
      n SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup)
    site directions →
  R187.eraseUnitQuaternion (Bond.pathHolonomy realization site directions)
  ≡ rawPathHolonomy realization site directions
erasePathHolonomy realization site [] = eraseIdentity
erasePathHolonomy realization site (direction ∷ directions) =
  trans
    (eraseMultiply
      (Bond.orientedLink realization site direction)
      (Bond.pathHolonomy realization (Bond.walkStep site direction) directions))
    (cong
      (λ tail →
        R187.eraseUnitQuaternion (Bond.orientedLink realization site direction)
        Q.*q tail)
      (erasePathHolonomy realization
        (Bond.walkStep site direction) directions))

selectedPhysicalPathHolonomyErasesExactly :
  ∀ background site directions →
  R187.eraseUnitQuaternion
    (Bond.pathHolonomy (R187.physicalBackgroundRealization background)
      site directions)
  ≡
  rawPathHolonomy (R187.physicalBackgroundRealization background)
    site directions
selectedPhysicalPathHolonomyErasesExactly = erasePathHolonomy

cmp98RawUnitIdentityHomomorphismRound189Level : ProofLevel
cmp98RawUnitIdentityHomomorphismRound189Level = machineChecked

cmp98RawUnitMultiplicationHomomorphismRound189Level : ProofLevel
cmp98RawUnitMultiplicationHomomorphismRound189Level = machineChecked

cmp98RawUnitInverseHomomorphismRound189Level : ProofLevel
cmp98RawUnitInverseHomomorphismRound189Level = machineChecked

cmp98RawUnitPathHolomorphismRound189Level : ProofLevel
cmp98RawUnitPathHolomorphismRound189Level = machineChecked

-- The former R187 conditional carrier seam is now reduced to downstream API
-- adaptation only: the exact periodic group/path object can be erased into the
-- raw Wilson quaternion product without changing any path product.  Do not
-- introduce an ExactLinkGroup on all raw quaternions merely to satisfy an old
-- interface; non-unit raw quaternions are not the physical SU(2) group.
