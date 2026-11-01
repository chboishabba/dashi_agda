module DASHI.Physics.YangMills.BalabanP33QuaternionChordalSquaredExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Build the algebraic core of the concrete SU(2) chordal metric directly on
-- the repository's unit-quaternion carrier.  For
--
--   delta(q,r) = ||q-r||_R4^2,
--
-- left and right multiplication by a unit quaternion preserve delta exactly.
-- The proof supplies the previously missing right distributivity and both
-- multiplication/negation laws by computed polynomial certificates, then uses
-- the already checked multiplicativity of the quaternion norm square.
--
-- This module deliberately stops at squared chordal distance.  Constructing
-- the nonnegative square root and proving its triangle inequality is a
-- distinct metric-completion task.  Keeping that seam visible prevents a
-- silent identification of local group chord distance with physical spacetime
-- distance in the later clustering theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  (module RealPolynomialSolver)
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  (solveComputed; computed)
open RealPolynomialSolver using (_:=_; _:+_; :-_)
open import DASHI.Physics.YangMills.BalabanQuaternionPolynomialIdentities using
  (q0R; q1R; q2R; q3R; q0P; q1P; q2P; q3P)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( Quaternion; quat; SU2Quaternion; quaternion; unitNormSquared
  ; _+q_; negQ; _*q_; normSquaredQ; quaternionExt
  ; quaternionNormMultiplicative
  ; _+R_; -R_; *-identityˡ; *-identityʳ
  )
open import DASHI.Physics.YangMills.BalabanP33QuaternionProductSecondVariationExact using
  (quaternionMultiplyDistributesLeft)

subQ : Quaternion → Quaternion → Quaternion
subQ left right = left +q negQ right

chordSquaredQ : Quaternion → Quaternion → ℝ
chordSquaredQ left right = normSquaredQ (subQ left right)

------------------------------------------------------------------------
-- Multiplication commutes with quaternion negation.
------------------------------------------------------------------------

leftMultiplyNeg0 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  q0R a0 a1 a2 a3
    (-R b0) (-R b1) (-R b2) (-R b3)
  ≡ -R q0R a0 a1 a2 a3 b0 b1 b2 b3
leftMultiplyNeg0 =
  solveComputed 8
    (λ a0 a1 a2 a3 b0 b1 b2 b3 →
      q0P a0 a1 a2 a3
        (:- b0) (:- b1) (:- b2) (:- b3)
      := :- (q0P a0 a1 a2 a3 b0 b1 b2 b3))
    computed

leftMultiplyNeg1 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  q1R a0 a1 a2 a3
    (-R b0) (-R b1) (-R b2) (-R b3)
  ≡ -R q1R a0 a1 a2 a3 b0 b1 b2 b3
leftMultiplyNeg1 =
  solveComputed 8
    (λ a0 a1 a2 a3 b0 b1 b2 b3 →
      q1P a0 a1 a2 a3
        (:- b0) (:- b1) (:- b2) (:- b3)
      := :- (q1P a0 a1 a2 a3 b0 b1 b2 b3))
    computed

leftMultiplyNeg2 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  q2R a0 a1 a2 a3
    (-R b0) (-R b1) (-R b2) (-R b3)
  ≡ -R q2R a0 a1 a2 a3 b0 b1 b2 b3
leftMultiplyNeg2 =
  solveComputed 8
    (λ a0 a1 a2 a3 b0 b1 b2 b3 →
      q2P a0 a1 a2 a3
        (:- b0) (:- b1) (:- b2) (:- b3)
      := :- (q2P a0 a1 a2 a3 b0 b1 b2 b3))
    computed

leftMultiplyNeg3 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  q3R a0 a1 a2 a3
    (-R b0) (-R b1) (-R b2) (-R b3)
  ≡ -R q3R a0 a1 a2 a3 b0 b1 b2 b3
leftMultiplyNeg3 =
  solveComputed 8
    (λ a0 a1 a2 a3 b0 b1 b2 b3 →
      q3P a0 a1 a2 a3
        (:- b0) (:- b1) (:- b2) (:- b3)
      := :- (q3P a0 a1 a2 a3 b0 b1 b2 b3))
    computed

quaternionMultiplyNegRight : ∀ left right →
  left *q negQ right ≡ negQ (left *q right)
quaternionMultiplyNegRight
    (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) =
  quaternionExt
    (leftMultiplyNeg0 a0 a1 a2 a3 b0 b1 b2 b3)
    (leftMultiplyNeg1 a0 a1 a2 a3 b0 b1 b2 b3)
    (leftMultiplyNeg2 a0 a1 a2 a3 b0 b1 b2 b3)
    (leftMultiplyNeg3 a0 a1 a2 a3 b0 b1 b2 b3)

rightMultiplyNeg0 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  q0R (-R a0) (-R a1) (-R a2) (-R a3)
    b0 b1 b2 b3
  ≡ -R q0R a0 a1 a2 a3 b0 b1 b2 b3
rightMultiplyNeg0 =
  solveComputed 8
    (λ a0 a1 a2 a3 b0 b1 b2 b3 →
      q0P (:- a0) (:- a1) (:- a2) (:- a3)
        b0 b1 b2 b3
      := :- (q0P a0 a1 a2 a3 b0 b1 b2 b3))
    computed

rightMultiplyNeg1 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  q1R (-R a0) (-R a1) (-R a2) (-R a3)
    b0 b1 b2 b3
  ≡ -R q1R a0 a1 a2 a3 b0 b1 b2 b3
rightMultiplyNeg1 =
  solveComputed 8
    (λ a0 a1 a2 a3 b0 b1 b2 b3 →
      q1P (:- a0) (:- a1) (:- a2) (:- a3)
        b0 b1 b2 b3
      := :- (q1P a0 a1 a2 a3 b0 b1 b2 b3))
    computed

rightMultiplyNeg2 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  q2R (-R a0) (-R a1) (-R a2) (-R a3)
    b0 b1 b2 b3
  ≡ -R q2R a0 a1 a2 a3 b0 b1 b2 b3
rightMultiplyNeg2 =
  solveComputed 8
    (λ a0 a1 a2 a3 b0 b1 b2 b3 →
      q2P (:- a0) (:- a1) (:- a2) (:- a3)
        b0 b1 b2 b3
      := :- (q2P a0 a1 a2 a3 b0 b1 b2 b3))
    computed

rightMultiplyNeg3 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  q3R (-R a0) (-R a1) (-R a2) (-R a3)
    b0 b1 b2 b3
  ≡ -R q3R a0 a1 a2 a3 b0 b1 b2 b3
rightMultiplyNeg3 =
  solveComputed 8
    (λ a0 a1 a2 a3 b0 b1 b2 b3 →
      q3P (:- a0) (:- a1) (:- a2) (:- a3)
        b0 b1 b2 b3
      := :- (q3P a0 a1 a2 a3 b0 b1 b2 b3))
    computed

quaternionNegMultiply : ∀ left right →
  negQ left *q right ≡ negQ (left *q right)
quaternionNegMultiply
    (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) =
  quaternionExt
    (rightMultiplyNeg0 a0 a1 a2 a3 b0 b1 b2 b3)
    (rightMultiplyNeg1 a0 a1 a2 a3 b0 b1 b2 b3)
    (rightMultiplyNeg2 a0 a1 a2 a3 b0 b1 b2 b3)
    (rightMultiplyNeg3 a0 a1 a2 a3 b0 b1 b2 b3)

------------------------------------------------------------------------
-- Missing right distributivity.
------------------------------------------------------------------------

rightDistributes0 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
  q0R (a0 +R b0) (a1 +R b1) (a2 +R b2) (a3 +R b3)
    c0 c1 c2 c3
  ≡ q0R a0 a1 a2 a3 c0 c1 c2 c3
      +R q0R b0 b1 b2 b3 c0 c1 c2 c3
rightDistributes0 =
  solveComputed 12
    (λ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
      q0P (a0 :+ b0) (a1 :+ b1) (a2 :+ b2) (a3 :+ b3)
        c0 c1 c2 c3
      := q0P a0 a1 a2 a3 c0 c1 c2 c3
          :+ q0P b0 b1 b2 b3 c0 c1 c2 c3)
    computed

rightDistributes1 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
  q1R (a0 +R b0) (a1 +R b1) (a2 +R b2) (a3 +R b3)
    c0 c1 c2 c3
  ≡ q1R a0 a1 a2 a3 c0 c1 c2 c3
      +R q1R b0 b1 b2 b3 c0 c1 c2 c3
rightDistributes1 =
  solveComputed 12
    (λ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
      q1P (a0 :+ b0) (a1 :+ b1) (a2 :+ b2) (a3 :+ b3)
        c0 c1 c2 c3
      := q1P a0 a1 a2 a3 c0 c1 c2 c3
          :+ q1P b0 b1 b2 b3 c0 c1 c2 c3)
    computed

rightDistributes2 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
  q2R (a0 +R b0) (a1 +R b1) (a2 +R b2) (a3 +R b3)
    c0 c1 c2 c3
  ≡ q2R a0 a1 a2 a3 c0 c1 c2 c3
      +R q2R b0 b1 b2 b3 c0 c1 c2 c3
rightDistributes2 =
  solveComputed 12
    (λ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
      q2P (a0 :+ b0) (a1 :+ b1) (a2 :+ b2) (a3 :+ b3)
        c0 c1 c2 c3
      := q2P a0 a1 a2 a3 c0 c1 c2 c3
          :+ q2P b0 b1 b2 b3 c0 c1 c2 c3)
    computed

rightDistributes3 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
  q3R (a0 +R b0) (a1 +R b1) (a2 +R b2) (a3 +R b3)
    c0 c1 c2 c3
  ≡ q3R a0 a1 a2 a3 c0 c1 c2 c3
      +R q3R b0 b1 b2 b3 c0 c1 c2 c3
rightDistributes3 =
  solveComputed 12
    (λ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
      q3P (a0 :+ b0) (a1 :+ b1) (a2 :+ b2) (a3 :+ b3)
        c0 c1 c2 c3
      := q3P a0 a1 a2 a3 c0 c1 c2 c3
          :+ q3P b0 b1 b2 b3 c0 c1 c2 c3)
    computed

quaternionMultiplyDistributesRight : ∀ left right multiplier →
  (left +q right) *q multiplier
  ≡ (left *q multiplier) +q (right *q multiplier)
quaternionMultiplyDistributesRight
    (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    (quat c0 c1 c2 c3) =
  quaternionExt
    (rightDistributes0 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3)
    (rightDistributes1 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3)
    (rightDistributes2 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3)
    (rightDistributes3 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3)

------------------------------------------------------------------------
-- Exact difference transport and squared-chord invariance.
------------------------------------------------------------------------

leftDifferenceTransportExact : ∀ g left right →
  g *q subQ left right
  ≡ subQ (g *q left) (g *q right)
leftDifferenceTransportExact g left right =
  trans
    (quaternionMultiplyDistributesLeft g left (negQ right))
    (cong ((g *q left) +q_)
      (quaternionMultiplyNegRight g right))

rightDifferenceTransportExact : ∀ g left right →
  subQ left right *q g
  ≡ subQ (left *q g) (right *q g)
rightDifferenceTransportExact g left right =
  trans
    (quaternionMultiplyDistributesRight left (negQ right) g)
    (cong ((left *q g) +q_)
      (quaternionNegMultiply right g))

chordSquaredLeftInvariant : ∀ g left right →
  chordSquaredQ
    (quaternion g *q left)
    (quaternion g *q right)
  ≡ chordSquaredQ left right
chordSquaredLeftInvariant g left right =
  trans
    (cong normSquaredQ
      (sym (leftDifferenceTransportExact (quaternion g) left right)))
    (trans
      (quaternionNormMultiplicative
        (quaternion g) (subQ left right))
      (trans
        (cong (λ norm → norm *R normSquaredQ (subQ left right))
          (unitNormSquared g))
        (*-identityˡ (normSquaredQ (subQ left right)))))

chordSquaredRightInvariant : ∀ g left right →
  chordSquaredQ
    (left *q quaternion g)
    (right *q quaternion g)
  ≡ chordSquaredQ left right
chordSquaredRightInvariant g left right =
  trans
    (cong normSquaredQ
      (sym (rightDifferenceTransportExact (quaternion g) left right)))
    (trans
      (quaternionNormMultiplicative
        (subQ left right) (quaternion g))
      (trans
        (cong (λ norm → normSquaredQ (subQ left right) *R norm)
          (unitNormSquared g))
        (*-identityʳ (normSquaredQ (subQ left right)))))

quaternionNegationMultiplicationLevel : ProofLevel
quaternionNegationMultiplicationLevel = machineChecked

quaternionRightDistributivityLevel : ProofLevel
quaternionRightDistributivityLevel = machineChecked

su2ChordSquaredBiInvarianceLevel : ProofLevel
su2ChordSquaredBiInvarianceLevel = machineChecked

chordSquareRootTriangleInputsLevel : ProofLevel
chordSquareRootTriangleInputsLevel = conditional

chordalToPhysicalDistanceComparisonInputsLevel : ProofLevel
chordalToPhysicalDistanceComparisonInputsLevel = conditional
