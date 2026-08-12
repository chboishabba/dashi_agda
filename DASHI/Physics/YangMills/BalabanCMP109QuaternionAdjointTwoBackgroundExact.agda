module DASHI.Physics.YangMills.BalabanCMP109QuaternionAdjointTwoBackgroundExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
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
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Close the exact two-background adjoint-transport step needed after the
-- contour product telescope.  For unit rational quaternions P,Q,
--
--   Ad_P X - Ad_Q X
--    = (P-Q) X P^-1 + Q X(P^-1-Q^-1),
--
-- and therefore, with the repository's square-root-free quaternion norm,
--
--   N(Ad_P X - Ad_Q X) <= 4 N(P-Q) N(X).
--
-- The inverse-difference norm is exactly the forward-difference norm because
-- inversion of unit SU(2) quaternions is conjugation.  Thus the physical
-- transport modulus is reduced to the contour-product difference alone.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Four
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointPerturbationExact as Adjoint

adjointDifference :
  Q.RationalQuaternion → Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
adjointDifference p q value =
  Four._-q_ (Adjoint.adjointTransport p value) (Adjoint.adjointTransport q value)

adjointDifferenceFactorization :
  Q.RationalQuaternion → Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
adjointDifferenceFactorization p q value =
  ((Four._-q_ p q) Q.*q
      (value Q.*q Physical.quaternionConjugate p))
  Q.+q
  (q Q.*q
    (value Q.*q
      (Four._-q_
        (Physical.quaternionConjugate p)
        (Physical.quaternionConjugate q))))

adjointDifferenceFactorizationExact : ∀ p q value →
  adjointDifference p q value ≡ adjointDifferenceFactorization p q value
adjointDifferenceFactorizationExact
    (Q.quat p0 p1 p2 p3)
    (Q.quat q0 q1 q2 q3)
    (Q.quat x0 x1 x2 x3) =
  Q.quaternionExt
    (ℚRing.solve-∀ p0 p1 p2 p3 q0 q1 q2 q3 x0 x1 x2 x3)
    (ℚRing.solve-∀ p0 p1 p2 p3 q0 q1 q2 q3 x0 x1 x2 x3)
    (ℚRing.solve-∀ p0 p1 p2 p3 q0 q1 q2 q3 x0 x1 x2 x3)
    (ℚRing.solve-∀ p0 p1 p2 p3 q0 q1 q2 q3 x0 x1 x2 x3)

conjugateDifferenceExact : ∀ p q →
  Four._-q_
    (Physical.quaternionConjugate p)
    (Physical.quaternionConjugate q)
  ≡ Physical.quaternionConjugate (Four._-q_ p q)
conjugateDifferenceExact
    (Q.quat p0 p1 p2 p3)
    (Q.quat q0 q1 q2 q3) =
  Q.quaternionExt
    (ℚRing.solve-∀ p0 q0)
    (ℚRing.solve-∀ p1 q1)
    (ℚRing.solve-∀ p2 q2)
    (ℚRing.solve-∀ p3 q3)

conjugateDifferenceNormSqExact : ∀ p q →
  Norm.normSq
    (Four._-q_
      (Physical.quaternionConjugate p)
      (Physical.quaternionConjugate q))
  ≡ Norm.normSq (Four._-q_ p q)
conjugateDifferenceNormSqExact p q =
  trans
    (cong Norm.normSq (conjugateDifferenceExact p q))
    (Norm.normSqConjugateExact (Four._-q_ p q))

unitAdjointDifferenceNormSqBound : ∀ p q value →
  Norm.normSq p ≡ + 1 / 1 →
  Norm.normSq q ≡ + 1 / 1 →
  Norm.normSq (adjointDifference p q value)
  ≤ (+ 4 / 1) * Norm.normSq (Four._-q_ p q) * Norm.normSq value
unitAdjointDifferenceNormSqBound p q value pUnit qUnit =
  let
    left = (Four._-q_ p q) Q.*q
      (value Q.*q Physical.quaternionConjugate p)
    right = q Q.*q
      (value Q.*q
        (Four._-q_
          (Physical.quaternionConjugate p)
          (Physical.quaternionConjugate q)))

    leftNorm :
      Norm.normSq left
      ≡ Norm.normSq (Four._-q_ p q) * Norm.normSq value
    leftNorm
      rewrite Norm.normSqMultiplyExact
        (Four._-q_ p q) (value Q.*q Physical.quaternionConjugate p)
        | Norm.normSqMultiplyExact value (Physical.quaternionConjugate p)
        | Norm.normSqConjugateExact p
        | pUnit =
      ℚRing.solve-∀ (Norm.normSq (Four._-q_ p q)) (Norm.normSq value)

    rightNorm :
      Norm.normSq right
      ≡ Norm.normSq (Four._-q_ p q) * Norm.normSq value
    rightNorm
      rewrite Norm.normSqMultiplyExact q
        (value Q.*q
          (Four._-q_
            (Physical.quaternionConjugate p)
            (Physical.quaternionConjugate q)))
        | Norm.normSqMultiplyExact value
          (Four._-q_
            (Physical.quaternionConjugate p)
            (Physical.quaternionConjugate q))
        | conjugateDifferenceNormSqExact p q
        | qUnit =
      ℚRing.solve-∀ (Norm.normSq (Four._-q_ p q)) (Norm.normSq value)

    sumBound = Norm.normSqAddBound left right
    factorizedBound :
      Norm.normSq (adjointDifferenceFactorization p q value)
      ≤ (+ 4 / 1) * Norm.normSq (Four._-q_ p q) * Norm.normSq value
    factorizedBound =
      subst
        (λ upper → Norm.normSq (left Q.+q right) ≤ upper)
        (ℚRing.solve-∀
          (Norm.normSq (Four._-q_ p q)) (Norm.normSq value))
        (subst
          (λ middle →
            Norm.normSq (left Q.+q right)
            ≤ (+ 2 / 1) * middle)
          (cong₂ _+_ leftNorm rightNorm)
          sumBound)
  in
  subst
    (λ lower →
      Norm.normSq lower
      ≤ (+ 4 / 1) * Norm.normSq (Four._-q_ p q) * Norm.normSq value)
    (sym (adjointDifferenceFactorizationExact p q value))
    factorizedBound

cmp109QuaternionAdjointTwoBackgroundIdentityLevel : ProofLevel
cmp109QuaternionAdjointTwoBackgroundIdentityLevel = machineChecked

cmp109QuaternionAdjointTwoBackgroundNormLevel : ProofLevel
cmp109QuaternionAdjointTwoBackgroundNormLevel = machineChecked
