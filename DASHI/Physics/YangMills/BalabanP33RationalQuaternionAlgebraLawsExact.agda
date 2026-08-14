module DASHI.Physics.YangMills.BalabanP33RationalQuaternionAlgebraLawsExact where

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
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- The earlier named Wilson atom development lived over DASHI's axiomatic real
-- carrier, whereas the literal finite Hessian and Combes--Thomas lane is over
-- exact rationals.  This module closes that carrier mismatch directly.
--
-- It constructs the concrete rational quaternion ring, proves the finite
-- noncommutative product rule, and shows that the second variation of an
-- ordered four-factor product is exactly
--
--   4 diagonal second-factor atoms
--     + 12 ordered first/first atoms.
--
-- Applying the Wilson convention S_p=1-q0(U_p) gives the exact scalar sum of
-- sixteen rational atom contributions.  At the flat background, with the two
-- inverse links represented by negative Lie-algebra insertions, the same
-- polynomial identity proves
--
--   S_p''(1)[h,h]
--     = ||X_0 + X_1 - X_2 - X_3||^2.
--
-- Thus the flat Wilson Hessian is literally the plaquette curl square, not an
-- abstract identification field.  The nonzero-background analytic estimate is
-- cleanly isolated as the difference between the same sixteen concrete atoms
-- and this flat curl square.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map; _++_; length)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionCoreExact public
quaternionAddAssociative : ∀ a b c →
  (a +q b) +q c ≡ a +q (b +q c)
quaternionAddAssociative
    (quat a0 a1 a2 a3)
    (quat b0 b1 b2 b3)
    (quat c0 c1 c2 c3) =
  quaternionExt
    (ℚP.+-assoc a0 b0 c0)
    (ℚP.+-assoc a1 b1 c1)
    (ℚP.+-assoc a2 b2 c2)
    (ℚP.+-assoc a3 b3 c3)

quaternionAddCommutative : ∀ a b → a +q b ≡ b +q a
quaternionAddCommutative
    (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) =
  quaternionExt
    (ℚP.+-comm a0 b0)
    (ℚP.+-comm a1 b1)
    (ℚP.+-comm a2 b2)
    (ℚP.+-comm a3 b3)

quaternionAddZeroLeft : ∀ a → zeroQ +q a ≡ a
quaternionAddZeroLeft (quat a0 a1 a2 a3) =
  quaternionExt
    (ℚP.+-identityˡ a0) (ℚP.+-identityˡ a1)
    (ℚP.+-identityˡ a2) (ℚP.+-identityˡ a3)

quaternionAddZeroRight : ∀ a → a +q zeroQ ≡ a
quaternionAddZeroRight a =
  trans (quaternionAddCommutative a zeroQ) (quaternionAddZeroLeft a)

quaternionMultiplyDistributesLeft : ∀ a b c →
  a *q (b +q c) ≡ (a *q b) +q (a *q c)
quaternionMultiplyDistributesLeft
    (quat a0 a1 a2 a3)
    (quat b0 b1 b2 b3)
    (quat c0 c1 c2 c3)
  rewrite q0Multiply (quat a0 a1 a2 a3)
    (quat b0 b1 b2 b3 +q quat c0 c1 c2 c3)
    | q0Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q0Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q1Multiply (quat a0 a1 a2 a3)
      (quat b0 b1 b2 b3 +q quat c0 c1 c2 c3)
    | q1Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q1Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q2Multiply (quat a0 a1 a2 a3)
      (quat b0 b1 b2 b3 +q quat c0 c1 c2 c3)
    | q2Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q2Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q3Multiply (quat a0 a1 a2 a3)
      (quat b0 b1 b2 b3 +q quat c0 c1 c2 c3)
    | q3Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q3Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q0Add (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q0Add
      ((quat a0 a1 a2 a3) *q (quat b0 b1 b2 b3))
      ((quat a0 a1 a2 a3) *q (quat c0 c1 c2 c3))
    | q1Add (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q1Add
      ((quat a0 a1 a2 a3) *q (quat b0 b1 b2 b3))
      ((quat a0 a1 a2 a3) *q (quat c0 c1 c2 c3))
    | q2Add (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q2Add
      ((quat a0 a1 a2 a3) *q (quat b0 b1 b2 b3))
      ((quat a0 a1 a2 a3) *q (quat c0 c1 c2 c3))
    | q3Add (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q3Add
      ((quat a0 a1 a2 a3) *q (quat b0 b1 b2 b3))
      ((quat a0 a1 a2 a3) *q (quat c0 c1 c2 c3))
    | q0Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q0Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q1Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q1Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q2Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q2Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q3Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q3Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3) =
  quaternionExt
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))

quaternionMultiplyDistributesRight : ∀ a b c →
  (a +q b) *q c ≡ (a *q c) +q (b *q c)
quaternionMultiplyDistributesRight
    (quat a0 a1 a2 a3)
    (quat b0 b1 b2 b3)
    (quat c0 c1 c2 c3)
  rewrite q0Multiply
      (quat a0 a1 a2 a3 +q quat b0 b1 b2 b3)
      (quat c0 c1 c2 c3)
    | q0Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q0Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q1Multiply
      (quat a0 a1 a2 a3 +q quat b0 b1 b2 b3)
      (quat c0 c1 c2 c3)
    | q1Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q1Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q2Multiply
      (quat a0 a1 a2 a3 +q quat b0 b1 b2 b3)
      (quat c0 c1 c2 c3)
    | q2Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q2Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q3Multiply
      (quat a0 a1 a2 a3 +q quat b0 b1 b2 b3)
      (quat c0 c1 c2 c3)
    | q3Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q3Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q0Add (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q0Add
      ((quat a0 a1 a2 a3) *q (quat c0 c1 c2 c3))
      ((quat b0 b1 b2 b3) *q (quat c0 c1 c2 c3))
    | q1Add (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q1Add
      ((quat a0 a1 a2 a3) *q (quat c0 c1 c2 c3))
      ((quat b0 b1 b2 b3) *q (quat c0 c1 c2 c3))
    | q2Add (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q2Add
      ((quat a0 a1 a2 a3) *q (quat c0 c1 c2 c3))
      ((quat b0 b1 b2 b3) *q (quat c0 c1 c2 c3))
    | q3Add (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q3Add
      ((quat a0 a1 a2 a3) *q (quat c0 c1 c2 c3))
      ((quat b0 b1 b2 b3) *q (quat c0 c1 c2 c3))
    | q0Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q0Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q1Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q1Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q2Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q2Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q3Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q3Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3) =
  quaternionExt
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))

quaternionMultiplyAssociative : ∀ a b c →
  (a *q b) *q c ≡ a *q (b *q c)
quaternionMultiplyAssociative
    (quat a0 a1 a2 a3)
    (quat b0 b1 b2 b3)
    (quat c0 c1 c2 c3)
  rewrite q0Multiply
      ((quat a0 a1 a2 a3) *q (quat b0 b1 b2 b3))
      (quat c0 c1 c2 c3)
    | q0Multiply (quat a0 a1 a2 a3)
      ((quat b0 b1 b2 b3) *q (quat c0 c1 c2 c3))
    | q0Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q0Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q1Multiply
      ((quat a0 a1 a2 a3) *q (quat b0 b1 b2 b3))
      (quat c0 c1 c2 c3)
    | q1Multiply (quat a0 a1 a2 a3)
      ((quat b0 b1 b2 b3) *q (quat c0 c1 c2 c3))
    | q1Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q1Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q2Multiply
      ((quat a0 a1 a2 a3) *q (quat b0 b1 b2 b3))
      (quat c0 c1 c2 c3)
    | q2Multiply (quat a0 a1 a2 a3)
      ((quat b0 b1 b2 b3) *q (quat c0 c1 c2 c3))
    | q2Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q2Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q3Multiply
      ((quat a0 a1 a2 a3) *q (quat b0 b1 b2 b3))
      (quat c0 c1 c2 c3)
    | q3Multiply (quat a0 a1 a2 a3)
      ((quat b0 b1 b2 b3) *q (quat c0 c1 c2 c3))
    | q3Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q3Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3) =
  quaternionExt
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))

quaternionMultiplyZeroRight : ∀ a → a *q zeroQ ≡ zeroQ
quaternionMultiplyZeroRight (quat a0 a1 a2 a3)
  rewrite q0Multiply (quat a0 a1 a2 a3) zeroQ
    | q1Multiply (quat a0 a1 a2 a3) zeroQ
    | q2Multiply (quat a0 a1 a2 a3) zeroQ
    | q3Multiply (quat a0 a1 a2 a3) zeroQ =
  quaternionExt
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))

------------------------------------------------------------------------
-- Ordered product jets and the exact sixteen atoms.
------------------------------------------------------------------------
