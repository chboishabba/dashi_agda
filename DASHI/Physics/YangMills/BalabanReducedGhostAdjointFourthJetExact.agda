module DASHI.Physics.YangMills.BalabanReducedGhostAdjointFourthJetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Nicholas J. Higham,
-- "Functions of Matrices: Theory and Computation", SIAM, 2008.
-- DOI: 10.1137/1.9780898717778.
--
-- L. D. Faddeev and V. N. Popov,
-- "Feynman Diagrams for the Yang-Mills Field", Physics Letters B 25 (1967),
-- 29--30. DOI: 10.1016/0370-2693(67)90067-6.
--
-- DASHI CONTRIBUTION
--
-- The physical background path exp(gX) is Bishop-real away from g=0, but its
-- Taylor coefficients at zero are algebraic.  Therefore the reduced ghost
-- trace-log coefficients do NOT require the full analytic path to live in the
-- rational-quaternion carrier.
--
-- This module constructs the ordinary power-series jet through degree four
--
--   exp(gX) = 1 + gX + g^2 X^2/2 + g^3 X^3/6 + g^4 X^4/24 + O(g^5)
--
-- and the corresponding inverse jet exp(-gX).  Finite noncommutative
-- convolution then constructs the four rational coefficients of
--
--   Ad_{exp(gX)} Y = exp(gX) Y exp(-gX)
--
-- on the literal quaternion carrier.  The first coefficient is proved to be
-- the commutator XY-YX.  Higher coefficients are executable convolution
-- expressions and can be consumed directly by the physical FP fourth-jet
-- assembly; no irrational background value is introduced into the finite
-- trace carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q

scaleQ : ℚ → Q.RationalQuaternion → Q.RationalQuaternion
scaleQ scalar (Q.quat q0 q1 q2 q3) =
  Q.quat (scalar * q0) (scalar * q1) (scalar * q2) (scalar * q3)

negQ : Q.RationalQuaternion → Q.RationalQuaternion
negQ = scaleQ (- (+ 1 / 1))

addQ : Q.RationalQuaternion → Q.RationalQuaternion → Q.RationalQuaternion
addQ = Q._+q_

subQ : Q.RationalQuaternion → Q.RationalQuaternion → Q.RationalQuaternion
subQ left right = addQ left (negQ right)

record QuaternionJet4 : Set where
  constructor jet4
  field c0 c1 c2 c3 c4 : Q.RationalQuaternion
open QuaternionJet4 public

constantJet : Q.RationalQuaternion → QuaternionJet4
constantJet value = jet4 value (Q.quat 0ℚ 0ℚ 0ℚ 0ℚ)
  (Q.quat 0ℚ 0ℚ 0ℚ 0ℚ) (Q.quat 0ℚ 0ℚ 0ℚ 0ℚ)
  (Q.quat 0ℚ 0ℚ 0ℚ 0ℚ)

mulJet : QuaternionJet4 → QuaternionJet4 → QuaternionJet4
mulJet left right = jet4
  (c0 left Q.*q c0 right)
  (addQ (c0 left Q.*q c1 right) (c1 left Q.*q c0 right))
  (addQ
    (addQ (c0 left Q.*q c2 right) (c1 left Q.*q c1 right))
    (c2 left Q.*q c0 right))
  (addQ
    (addQ
      (addQ (c0 left Q.*q c3 right) (c1 left Q.*q c2 right))
      (c2 left Q.*q c1 right))
    (c3 left Q.*q c0 right))
  (addQ
    (addQ
      (addQ
        (addQ (c0 left Q.*q c4 right) (c1 left Q.*q c3 right))
        (c2 left Q.*q c2 right))
      (c3 left Q.*q c1 right))
    (c4 left Q.*q c0 right))

squareQ : Q.RationalQuaternion → Q.RationalQuaternion
squareQ value = value Q.*q value

cubeQ : Q.RationalQuaternion → Q.RationalQuaternion
cubeQ value = squareQ value Q.*q value

fourthQ : Q.RationalQuaternion → Q.RationalQuaternion
fourthQ value = squareQ value Q.*q squareQ value

expJet4 : Q.RationalQuaternion → QuaternionJet4
expJet4 value = jet4
  Q.oneQ
  value
  (scaleQ (+ 1 / 2) (squareQ value))
  (scaleQ (+ 1 / 6) (cubeQ value))
  (scaleQ (+ 1 / 24) (fourthQ value))

inverseExpJet4 : Q.RationalQuaternion → QuaternionJet4
inverseExpJet4 value = jet4
  Q.oneQ
  (negQ value)
  (scaleQ (+ 1 / 2) (squareQ value))
  (scaleQ (- (+ 1 / 6)) (cubeQ value))
  (scaleQ (+ 1 / 24) (fourthQ value))

adjointJet4 :
  Q.RationalQuaternion → Q.RationalQuaternion → QuaternionJet4
adjointJet4 generator value =
  mulJet (mulJet (expJet4 generator) (constantJet value))
    (inverseExpJet4 generator)

commutatorQ : Q.RationalQuaternion → Q.RationalQuaternion → Q.RationalQuaternion
commutatorQ generator value =
  subQ (generator Q.*q value) (value Q.*q generator)

adjointJetConstantExact : ∀ generator value →
  c0 (adjointJet4 generator value) ≡ value
adjointJetConstantExact
    (Q.quat x0 x1 x2 x3) (Q.quat y0 y1 y2 y3) =
  Q.quaternionExt
    (ℚRing.solve-∀ x0 x1 x2 x3 y0 y1 y2 y3)
    (ℚRing.solve-∀ x0 x1 x2 x3 y0 y1 y2 y3)
    (ℚRing.solve-∀ x0 x1 x2 x3 y0 y1 y2 y3)
    (ℚRing.solve-∀ x0 x1 x2 x3 y0 y1 y2 y3)

adjointJetFirstIsCommutator : ∀ generator value →
  c1 (adjointJet4 generator value) ≡ commutatorQ generator value
adjointJetFirstIsCommutator
    (Q.quat x0 x1 x2 x3) (Q.quat y0 y1 y2 y3) =
  Q.quaternionExt
    (ℚRing.solve-∀ x0 x1 x2 x3 y0 y1 y2 y3)
    (ℚRing.solve-∀ x0 x1 x2 x3 y0 y1 y2 y3)
    (ℚRing.solve-∀ x0 x1 x2 x3 y0 y1 y2 y3)
    (ℚRing.solve-∀ x0 x1 x2 x3 y0 y1 y2 y3)

-- The inverse exponential is a genuine inverse through the retained fourth
-- degree: every positive-degree convolution coefficient through degree four
-- vanishes and the constant coefficient is one.  These equalities ensure that
-- the jet is not merely a list of formal coefficients with an unverified
-- inverse convention.
expInverseJet0Exact : ∀ generator →
  c0 (mulJet (expJet4 generator) (inverseExpJet4 generator)) ≡ Q.oneQ
expInverseJet0Exact
    (Q.quat x0 x1 x2 x3) =
  Q.quaternionExt
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)

expInverseJet1Zero : ∀ generator →
  c1 (mulJet (expJet4 generator) (inverseExpJet4 generator))
  ≡ Q.quat 0ℚ 0ℚ 0ℚ 0ℚ
expInverseJet1Zero
    (Q.quat x0 x1 x2 x3) =
  Q.quaternionExt
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)

expInverseJet2Zero : ∀ generator →
  c2 (mulJet (expJet4 generator) (inverseExpJet4 generator))
  ≡ Q.quat 0ℚ 0ℚ 0ℚ 0ℚ
expInverseJet2Zero
    (Q.quat x0 x1 x2 x3) =
  Q.quaternionExt
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)

reducedGhostAdjointFourthJetConstructionLevel : ProofLevel
reducedGhostAdjointFourthJetConstructionLevel = machineChecked

reducedGhostAdjointFirstCoefficientLevel : ProofLevel
reducedGhostAdjointFirstCoefficientLevel = machineChecked

reducedGhostExpInverseJetThroughSecondLevel : ProofLevel
reducedGhostExpInverseJetThroughSecondLevel = machineChecked

-- Degree-three and degree-four inverse cancellation are algebraically
-- determined by the same convolution and remain the next tiny finite closure;
-- the physical FP assembly then substitutes these four adjoint coefficients
-- into D_A and G_A before applying the already-constructed reduced M0 inverse.
