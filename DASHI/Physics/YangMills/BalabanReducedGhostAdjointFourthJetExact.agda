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
-- and its inverse.  Noncommutative convolution constructs
--
--   Ad_{exp(gX)}Y = exp(gX)Yexp(-gX),
--
-- and the four retained coefficients are proved exactly to be
--
--   ad_X Y,
--   (1/2) ad_X^2 Y,
--   (1/6) ad_X^3 Y,
--   (1/24) ad_X^4 Y.
--
-- Thus all four coefficient matrices required by the finite ghost trace-log
-- are rational whenever the tangent insertions are rational, despite the
-- nonzero-g background itself living naturally on the Bishop-real carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q

zeroQ : Q.RationalQuaternion
zeroQ = Q.quat 0ℚ 0ℚ 0ℚ 0ℚ

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
constantJet value = jet4 value zeroQ zeroQ zeroQ zeroQ

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
  Q.oneQ value
  (scaleQ (+ 1 / 2) (squareQ value))
  (scaleQ (+ 1 / 6) (cubeQ value))
  (scaleQ (+ 1 / 24) (fourthQ value))

inverseExpJet4 : Q.RationalQuaternion → QuaternionJet4
inverseExpJet4 value = jet4
  Q.oneQ (negQ value)
  (scaleQ (+ 1 / 2) (squareQ value))
  (scaleQ (- (+ 1 / 6)) (cubeQ value))
  (scaleQ (+ 1 / 24) (fourthQ value))

adjointJet4 : Q.RationalQuaternion → Q.RationalQuaternion → QuaternionJet4
adjointJet4 generator value =
  mulJet (mulJet (expJet4 generator) (constantJet value))
    (inverseExpJet4 generator)

commutatorQ : Q.RationalQuaternion → Q.RationalQuaternion → Q.RationalQuaternion
commutatorQ generator value =
  subQ (generator Q.*q value) (value Q.*q generator)

ad2Q ad3Q ad4Q :
  Q.RationalQuaternion → Q.RationalQuaternion → Q.RationalQuaternion
ad2Q generator value = commutatorQ generator (commutatorQ generator value)
ad3Q generator value = commutatorQ generator (ad2Q generator value)
ad4Q generator value = commutatorQ generator (ad3Q generator value)

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

adjointJetSecondIsHalfAd2 : ∀ generator value →
  c2 (adjointJet4 generator value) ≡ scaleQ (+ 1 / 2) (ad2Q generator value)
adjointJetSecondIsHalfAd2
    (Q.quat x0 x1 x2 x3) (Q.quat y0 y1 y2 y3) =
  Q.quaternionExt
    (ℚRing.solve-∀ x0 x1 x2 x3 y0 y1 y2 y3)
    (ℚRing.solve-∀ x0 x1 x2 x3 y0 y1 y2 y3)
    (ℚRing.solve-∀ x0 x1 x2 x3 y0 y1 y2 y3)
    (ℚRing.solve-∀ x0 x1 x2 x3 y0 y1 y2 y3)

adjointJetThirdIsSixthAd3 : ∀ generator value →
  c3 (adjointJet4 generator value) ≡ scaleQ (+ 1 / 6) (ad3Q generator value)
adjointJetThirdIsSixthAd3
    (Q.quat x0 x1 x2 x3) (Q.quat y0 y1 y2 y3) =
  Q.quaternionExt
    (ℚRing.solve-∀ x0 x1 x2 x3 y0 y1 y2 y3)
    (ℚRing.solve-∀ x0 x1 x2 x3 y0 y1 y2 y3)
    (ℚRing.solve-∀ x0 x1 x2 x3 y0 y1 y2 y3)
    (ℚRing.solve-∀ x0 x1 x2 x3 y0 y1 y2 y3)

adjointJetFourthIsTwentyFourthAd4 : ∀ generator value →
  c4 (adjointJet4 generator value) ≡ scaleQ (+ 1 / 24) (ad4Q generator value)
adjointJetFourthIsTwentyFourthAd4
    (Q.quat x0 x1 x2 x3) (Q.quat y0 y1 y2 y3) =
  Q.quaternionExt
    (ℚRing.solve-∀ x0 x1 x2 x3 y0 y1 y2 y3)
    (ℚRing.solve-∀ x0 x1 x2 x3 y0 y1 y2 y3)
    (ℚRing.solve-∀ x0 x1 x2 x3 y0 y1 y2 y3)
    (ℚRing.solve-∀ x0 x1 x2 x3 y0 y1 y2 y3)

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
  c1 (mulJet (expJet4 generator) (inverseExpJet4 generator)) ≡ zeroQ
expInverseJet1Zero
    (Q.quat x0 x1 x2 x3) =
  Q.quaternionExt
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)

expInverseJet2Zero : ∀ generator →
  c2 (mulJet (expJet4 generator) (inverseExpJet4 generator)) ≡ zeroQ
expInverseJet2Zero
    (Q.quat x0 x1 x2 x3) =
  Q.quaternionExt
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)

expInverseJet3Zero : ∀ generator →
  c3 (mulJet (expJet4 generator) (inverseExpJet4 generator)) ≡ zeroQ
expInverseJet3Zero
    (Q.quat x0 x1 x2 x3) =
  Q.quaternionExt
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)

expInverseJet4Zero : ∀ generator →
  c4 (mulJet (expJet4 generator) (inverseExpJet4 generator)) ≡ zeroQ
expInverseJet4Zero
    (Q.quat x0 x1 x2 x3) =
  Q.quaternionExt
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)

reducedGhostAdjointFourthJetConstructionLevel : ProofLevel
reducedGhostAdjointFourthJetConstructionLevel = machineChecked

reducedGhostAdjointAllFourCoefficientIdentificationLevel : ProofLevel
reducedGhostAdjointAllFourCoefficientIdentificationLevel = machineChecked

reducedGhostExpInverseJetThroughFourthLevel : ProofLevel
reducedGhostExpInverseJetThroughFourthLevel = machineChecked

-- Remaining ghost work: assemble these exact linkwise adjoint coefficients
-- through the literal D_A and G_A finite sums, postcompose with the existing
-- reduced M0 inverse, and prove the Bishop-real O(g^5) remainder/log-det
-- convergence on the selected weak-coupling ball.
