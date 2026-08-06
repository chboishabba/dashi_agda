module DASHI.Physics.YangMills.BalabanP33WilsonCrossOperatorPythagoreanExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks",
-- Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- Give the factorised Wilson cross operator an exact norm identity.  For unit
-- background quaternions u and v and a pure-imaginary insertion Y, set
--
--   W = (u Y) v.
--
-- Quaternion norm multiplicativity and unit norms prove
--
--   q0(W)^2 + ||Im(W)||^2 = ||Y||^2.
--
-- Thus the concrete cross operator Y |-> Im((u Y)v) is a Euclidean
-- contraction; the usual inequality follows solely by dropping the
-- nonnegative scalar square.  This module proves the stronger Pythagorean
-- equality, avoiding a new operator-norm premise.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanRealPolynomialRing using
  (_+R_; _*R_; zeroR)
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  (module RealPolynomialSolver)
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  (solveComputed; computed)
open RealPolynomialSolver using (_:=_; _:+_; _:*_)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( Quaternion; quat; SU2Quaternion; quaternion
  ; _*q_; q0; q1; q2; q3
  ; quaternionNormSquared; quaternionNormSquaredMultiply
  ; unitNormSquared
  )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (SU2LieAlgebra; su2Lie; lieQuaternion)
open import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct using
  (su2Dot)
import DASHI.Physics.YangMills.BalabanP33SU2EuclideanGeometryExact as Euclidean
import DASHI.Physics.YangMills.BalabanP33WilsonTransportedInnerProductExact as Pairing

quaternionNormDecomposes : ∀ value →
  quaternionNormSquared value
  ≡ (q0 value *R q0 value)
      +R Euclidean.su2NormSq (Pairing.quaternionImaginaryPart value)
quaternionNormDecomposes (quat scalar x y z) =
  solveComputed 4
    (λ scalar x y z →
      (((scalar :* scalar) :+ (x :* x)) :+ (y :* y)) :+ (z :* z)
      := (scalar :* scalar)
        :+ (((x :* x) :+ (y :* y)) :+ (z :* z)))
    computed scalar x y z

pureImaginaryQuaternionNormExact : ∀ Y →
  quaternionNormSquared (lieQuaternion Y) ≡ Euclidean.su2NormSq Y
pureImaginaryQuaternionNormExact (su2Lie x y z) =
  solveComputed 3
    (λ x y z →
      (((zeroR :* zeroR) :+ (x :* x)) :+ (y :* y)) :+ (z :* z)
      := ((x :* x) :+ (y :* y)) :+ (z :* z))
    computed x y z

unitSandwichQuaternionNormExact : ∀ left Y right →
  quaternionNormSquared
    ((quaternion left *q lieQuaternion Y) *q quaternion right)
  ≡ Euclidean.su2NormSq Y
unitSandwichQuaternionNormExact left Y right =
  trans
    (quaternionNormSquaredMultiply
      (quaternion left *q lieQuaternion Y) (quaternion right))
    (trans
      (cong
        (λ firstNorm →
          firstNorm *R quaternionNormSquared (quaternion right))
        (quaternionNormSquaredMultiply
          (quaternion left) (lieQuaternion Y)))
      (trans
        (cong
          (λ leftNorm →
            (leftNorm *R quaternionNormSquared (lieQuaternion Y))
            *R quaternionNormSquared (quaternion right))
          (unitNormSquared left))
        (trans
          (cong
            (λ rightNorm →
              ((DASHI.Physics.YangMills.BalabanRealPolynomialRing.oneR
                *R quaternionNormSquared (lieQuaternion Y)) *R rightNorm))
            (unitNormSquared right))
          (trans
            (cong
              (λ middle →
                (DASHI.Physics.YangMills.BalabanRealPolynomialRing.oneR
                  *R middle)
                *R DASHI.Physics.YangMills.BalabanRealPolynomialRing.oneR)
              (pureImaginaryQuaternionNormExact Y))
            (solveComputed 1
              (λ norm →
                ((DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
                    DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.oneCoefficient
                  :* norm)
                  :* DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
                    DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.oneCoefficient)
                := norm)
              computed (Euclidean.su2NormSq Y))))))

unitSandwichImaginaryPythagorean : ∀ left Y right →
  (q0 ((quaternion left *q lieQuaternion Y) *q quaternion right)
    *R q0 ((quaternion left *q lieQuaternion Y) *q quaternion right))
  +R Euclidean.su2NormSq
      (Pairing.quaternionImaginaryPart
        ((quaternion left *q lieQuaternion Y) *q quaternion right))
  ≡ Euclidean.su2NormSq Y
unitSandwichImaginaryPythagorean left Y right =
  trans
    (sym
      (quaternionNormDecomposes
        ((quaternion left *q lieQuaternion Y) *q quaternion right)))
    (unitSandwichQuaternionNormExact left Y right)

wilsonCrossQuaternionNormLevel : ProofLevel
wilsonCrossQuaternionNormLevel = machineChecked

wilsonCrossOperatorPythagoreanLevel : ProofLevel
wilsonCrossOperatorPythagoreanLevel = machineChecked
