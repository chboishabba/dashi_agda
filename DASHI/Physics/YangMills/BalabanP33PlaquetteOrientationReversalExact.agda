module DASHI.Physics.YangMills.BalabanP33PlaquetteOrientationReversalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- John H. Conway and Derek A. Smith,
-- "On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry",
-- A K Peters, 2003.
-- DOI: 10.1201/9781439864180.
--
-- DASHI CONTRIBUTION
--
-- Prove the literal quaternion transport underlying plaquette orientation
-- reversal.  Conjugation is involutive and reverses multiplication order.
-- Consequently the reverse of every ordered four-factor Wilson atom is the
-- conjugate of the original atom and has exactly the same scalar Wilson value.
-- The theorem is factor-pattern agnostic, so it applies without separate
-- assumptions to singleton, pair, triple and quartic subset atoms.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope

reverseQuaternion : Q.RationalQuaternion → Q.RationalQuaternion
reverseQuaternion = Physical.quaternionConjugate

reverseQuaternionInvolutive : ∀ value →
  reverseQuaternion (reverseQuaternion value) ≡ value
reverseQuaternionInvolutive (Q.quat q0 q1 q2 q3) =
  Q.quaternionExt
    (ℚRing.solve-∀ q0 q1 q2 q3)
    (ℚRing.solve-∀ q0 q1 q2 q3)
    (ℚRing.solve-∀ q0 q1 q2 q3)
    (ℚRing.solve-∀ q0 q1 q2 q3)

reverseQuaternionMultiply : ∀ left right →
  reverseQuaternion (left Q.*q right)
  ≡ reverseQuaternion right Q.*q reverseQuaternion left
reverseQuaternionMultiply
    (Q.quat a0 a1 a2 a3)
    (Q.quat b0 b1 b2 b3) =
  Q.quaternionExt
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)

reverseQuaternionAdd : ∀ left right →
  reverseQuaternion (left Q.+q right)
  ≡ reverseQuaternion left Q.+q reverseQuaternion right
reverseQuaternionAdd
    (Q.quat a0 a1 a2 a3)
    (Q.quat b0 b1 b2 b3) =
  Q.quaternionExt
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)

reverseFactorDefect : ∀ a b →
  reverseQuaternion (Telescope._-q_ a b)
  ≡ Telescope._-q_ (reverseQuaternion a) (reverseQuaternion b)
reverseFactorDefect
    (Q.quat a0 a1 a2 a3)
    (Q.quat b0 b1 b2 b3) =
  Q.quaternionExt
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)

reverseOrderedProduct4 :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
reverseOrderedProduct4 a0 a1 a2 a3 =
  Telescope.orderedProduct4
    (reverseQuaternion a3)
    (reverseQuaternion a2)
    (reverseQuaternion a1)
    (reverseQuaternion a0)

reverseSubsetAtomExact : ∀ a0 a1 a2 a3 →
  reverseQuaternion (Telescope.orderedProduct4 a0 a1 a2 a3)
  ≡ reverseOrderedProduct4 a0 a1 a2 a3
reverseSubsetAtomExact
    (Q.quat a00 a01 a02 a03)
    (Q.quat a10 a11 a12 a13)
    (Q.quat a20 a21 a22 a23)
    (Q.quat a30 a31 a32 a33) =
  Q.quaternionExt
    (ℚRing.solve-∀
      a00 a01 a02 a03 a10 a11 a12 a13
      a20 a21 a22 a23 a30 a31 a32 a33)
    (ℚRing.solve-∀
      a00 a01 a02 a03 a10 a11 a12 a13
      a20 a21 a22 a23 a30 a31 a32 a33)
    (ℚRing.solve-∀
      a00 a01 a02 a03 a10 a11 a12 a13
      a20 a21 a22 a23 a30 a31 a32 a33)
    (ℚRing.solve-∀
      a00 a01 a02 a03 a10 a11 a12 a13
      a20 a21 a22 a23 a30 a31 a32 a33)

reverseSingletonAtomExact :
  ∀ singleton0 singleton1 singleton2 singleton3 →
  reverseQuaternion
    (Telescope.orderedProduct4
      singleton0 singleton1 singleton2 singleton3)
  ≡ reverseOrderedProduct4
      singleton0 singleton1 singleton2 singleton3
reverseSingletonAtomExact = reverseSubsetAtomExact

reversePairAtomExact :
  ∀ pair0 pair1 pair2 pair3 →
  reverseQuaternion
    (Telescope.orderedProduct4 pair0 pair1 pair2 pair3)
  ≡ reverseOrderedProduct4 pair0 pair1 pair2 pair3
reversePairAtomExact = reverseSubsetAtomExact

reverseDeepAtomExact :
  ∀ deep0 deep1 deep2 deep3 →
  reverseQuaternion
    (Telescope.orderedProduct4 deep0 deep1 deep2 deep3)
  ≡ reverseOrderedProduct4 deep0 deep1 deep2 deep3
reverseDeepAtomExact = reverseSubsetAtomExact

reverseQuaternionScalarInvariant : ∀ value →
  Q.q0 (reverseQuaternion value) ≡ Q.q0 value
reverseQuaternionScalarInvariant (Q.quat q0 q1 q2 q3) =
  ℚRing.solve-∀ q0 q1 q2 q3

reverseWilsonScalarInvariant : ∀ value →
  Telescope.wilsonScalar (reverseQuaternion value)
  ≡ Telescope.wilsonScalar value
reverseWilsonScalarInvariant value =
  cong (λ selected → - selected)
    (reverseQuaternionScalarInvariant value)

reverseOrderedWilsonAtomInvariant : ∀ a0 a1 a2 a3 →
  Telescope.wilsonScalar (reverseOrderedProduct4 a0 a1 a2 a3)
  ≡ Telescope.wilsonScalar
      (Telescope.orderedProduct4 a0 a1 a2 a3)
reverseOrderedWilsonAtomInvariant a0 a1 a2 a3 =
  trans
    (cong Telescope.wilsonScalar
      (sym (reverseSubsetAtomExact a0 a1 a2 a3)))
    (reverseWilsonScalarInvariant
      (Telescope.orderedProduct4 a0 a1 a2 a3))

reverseOrderedProduct4Involutive : ∀ a0 a1 a2 a3 →
  reverseOrderedProduct4
    (reverseQuaternion a3)
    (reverseQuaternion a2)
    (reverseQuaternion a1)
    (reverseQuaternion a0)
  ≡ Telescope.orderedProduct4 a0 a1 a2 a3
reverseOrderedProduct4Involutive
    (Q.quat a00 a01 a02 a03)
    (Q.quat a10 a11 a12 a13)
    (Q.quat a20 a21 a22 a23)
    (Q.quat a30 a31 a32 a33) =
  Q.quaternionExt
    (ℚRing.solve-∀
      a00 a01 a02 a03 a10 a11 a12 a13
      a20 a21 a22 a23 a30 a31 a32 a33)
    (ℚRing.solve-∀
      a00 a01 a02 a03 a10 a11 a12 a13
      a20 a21 a22 a23 a30 a31 a32 a33)
    (ℚRing.solve-∀
      a00 a01 a02 a03 a10 a11 a12 a13
      a20 a21 a22 a23 a30 a31 a32 a33)
    (ℚRing.solve-∀
      a00 a01 a02 a03 a10 a11 a12 a13
      a20 a21 a22 a23 a30 a31 a32 a33)

plaquetteOrientationReversalQuaternionLevel : ProofLevel
plaquetteOrientationReversalQuaternionLevel = machineChecked

plaquetteOrientationReversalWilsonScalarLevel : ProofLevel
plaquetteOrientationReversalWilsonScalarLevel = machineChecked
