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
-- The proof is componentwise polynomial arithmetic plus the already proved
-- quaternion norm multiplicativity; it does not assume matrix unitarity.
--
-- The radial quaternion q=(c,su), ||u||^2=1, c^2+s^2=1 also satisfies
--
--   delta(q,1)=2(1-c).
--
-- Therefore for c=cos theta the usual chord/geodesic relation is
-- delta=4 sin^2(theta/2).  This module deliberately exposes squared chordal
-- distance: the square-root/triangle layer is kept separate so no silent
-- switch is made between group chord distance and physical spacetime distance.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  (module RealPolynomialSolver; zeroCoefficient)
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  (solveComputed; computed)
open RealPolynomialSolver using
  (Polynomial; con; _:=_; _:+_; _:*_; :-_)
open import DASHI.Physics.YangMills.BalabanQuaternionPolynomialIdentities using
  (q0P; q1P; q2P; q3P)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( Quaternion; quat; SU2Quaternion; quaternion; unitNormSquared
  ; zeroQ; oneQ; _+q_; negQ; _*q_; normSquaredQ; quaternionExt
  ; quaternionNormMultiplicative
  ; _+R_; _*R_; -R_; zeroR; oneR
  ; *-identityˡ
  )
open import DASHI.Physics.YangMills.BalabanP33QuaternionProductSecondVariationExact using
  (quaternionMultiplyDistributesLeft)

zeroP : ∀ {n} → Polynomial n
zeroP = con zeroCoefficient

subQ : Quaternion → Quaternion → Quaternion
subQ left right = left +q negQ right

chordSquaredQ : Quaternion → Quaternion → _
chordSquaredQ left right = normSquaredQ (subQ left right)

leftMultiplyNeg0 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  q0P a0 a1 a2 a3
    (:- b0) (:- b1) (:- b2) (:- b3)
  := :- (q0P a0 a1 a2 a3 b0 b1 b2 b3)
leftMultiplyNeg0 =
  solveComputed 8
    (λ a0 a1 a2 a3 b0 b1 b2 b3 →
      q0P a0 a1 a2 a3 (:- b0) (:- b1) (:- b2) (:- b3)
      := :- (q0P a0 a1 a2 a3 b0 b1 b2 b3))
    computed

leftMultiplyNeg1 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  q1P a0 a1 a2 a3
    (:- b0) (:- b1) (:- b2) (:- b3)
  := :- (q1P a0 a1 a2 a3 b0 b1 b2 b3)
leftMultiplyNeg1 =
  solveComputed 8
    (λ a0 a1 a2 a3 b0 b1 b2 b3 →
      q1P a0 a1 a2 a3 (:- b0) (:- b1) (:- b2) (:- b3)
      := :- (q1P a0 a1 a2 a3 b0 b1 b2 b3))
    computed

leftMultiplyNeg2 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  q2P a0 a1 a2 a3
    (:- b0) (:- b1) (:- b2) (:- b3)
  := :- (q2P a0 a1 a2 a3 b0 b1 b2 b3)
leftMultiplyNeg2 =
  solveComputed 8
    (λ a0 a1 a2 a3 b0 b1 b2 b3 →
      q2P a0 a1 a2 a3 (:- b0) (:- b1) (:- b2) (:- b3)
      := :- (q2P a0 a1 a2 a3 b0 b1 b2 b3))
    computed

leftMultiplyNeg3 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  q3P a0 a1 a2 a3
    (:- b0) (:- b1) (:- b2) (:- b3)
  := :- (q3P a0 a1 a2 a3 b0 b1 b2 b3)
leftMultiplyNeg3 =
  solveComputed 8
    (λ a0 a1 a2 a3 b0 b1 b2 b3 →
      q3P a0 a1 a2 a3 (:- b0) (:- b1) (:- b2) (:- b3)
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

rightDistributes0 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
  q0P (a0 :+ b0) (a1 :+ b1) (a2 :+ b2) (a3 :+ b3)
    c0 c1 c2 c3
  := q0P a0 a1 a2 a3 c0 c1 c2 c3
      :+ q0P b0 b1 b2 b3 c0 c1 c2 c3
rightDistributes0 =
  solveComputed 12
    (λ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
      q0P (a0 :+ b0) (a1 :+ b1) (a2 :+ b2) (a3 :+ b3)
        c0 c1 c2 c3
      := q0P a0 a1 a2 a3 c0 c1 c2 c3
          :+ q0P b0 b1 b2 b3 c0 c1 c2 c3)
    computed

rightDistributes1 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
  q1P (a0 :+ b0) (a1 :+ b1) (a2 :+ b2) (a3 :+ b3)
    c0 c1 c2 c3
  := q1P a0 a1 a2 a3 c0 c1 c2 c3
      :+ q1P b0 b1 b2 b3 c0 c1 c2 c3
rightDistributes1 =
  solveComputed 12
    (λ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
      q1P (a0 :+ b0) (a1 :+ b1) (a2 :+ b2) (a3 :+ b3)
        c0 c1 c2 c3
      := q1P a0 a1 a2 a3 c0 c1 c2 c3
          :+ q1P b0 b1 b2 b3 c0 c1 c2 c3)
    computed

rightDistributes2 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
  q2P (a0 :+ b0) (a1 :+ b1) (a2 :+ b2) (a3 :+ b3)
    c0 c1 c2 c3
  := q2P a0 a1 a2 a3 c0 c1 c2 c3
      :+ q2P b0 b1 b2 b3 c0 c1 c2 c3
rightDistributes2 =
  solveComputed 12
    (λ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
      q2P (a0 :+ b0) (a1 :+ b1) (a2 :+ b2) (a3 :+ b3)
        c0 c1 c2 c3
      := q2P a0 a1 a2 a3 c0 c1 c2 c3
          :+ q2P b0 b1 b2 b3 c0 c1 c2 c3)
    computed

rightDistributes3 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
  q3P (a0 :+ b0) (a1 :+ b1) (a2 :+ b2) (a3 :+ b3)
    c0 c1 c2 c3
  := q3P a0 a1 a2 a3 c0 c1 c2 c3
      :+ q3P b0 b1 b2 b3 c0 c1 c2 c3
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

quaternionNegMultiply : ∀ left right →
  negQ left *q right ≡ negQ (left *q right)
quaternionNegMultiply
    (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) =
  quaternionExt
    (solveComputed 8
      (λ a0 a1 a2 a3 b0 b1 b2 b3 →
        q0P (:- a0) (:- a1) (:- a2) (:- a3) b0 b1 b2 b3
        := :- (q0P a0 a1 a2 a3 b0 b1 b2 b3))
      computed a0 a1 a2 a3 b0 b1 b2 b3)
    (solveComputed 8
      (λ a0 a1 a2 a3 b0 b1 b2 b3 →
        q1P (:- a0) (:- a1) (:- a2) (:- a3) b0 b1 b2 b3
        := :- (q1P a0 a1 a2 a3 b0 b1 b2 b3))
      computed a0 a1 a2 a3 b0 b1 b2 b3)
    (solveComputed 8
      (λ a0 a1 a2 a3 b0 b1 b2 b3 →
        q2P (:- a0) (:- a1) (:- a2) (:- a3) b0 b1 b2 b3
        := :- (q2P a0 a1 a2 a3 b0 b1 b2 b3))
      computed a0 a1 a2 a3 b0 b1 b2 b3)
    (solveComputed 8
      (λ a0 a1 a2 a3 b0 b1 b2 b3 →
        q3P (:- a0) (:- a1) (:- a2) (:- a3) b0 b1 b2 b3
        := :- (q3P a0 a1 a2 a3 b0 b1 b2 b3))
      computed a0 a1 a2 a3 b0 b1 b2 b3)

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
        (cong (_*R normSquaredQ (subQ left right))
          (unitNormSquared g))
        (*-identityˡ (normSquaredQ (subQ left right))))))

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
        (cong (normSquaredQ (subQ left right) *R_)
          (unitNormSquared g))
        (DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier.*-identityʳ
          (normSquaredQ (subQ left right))))))

------------------------------------------------------------------------
-- Exact radial formula.
------------------------------------------------------------------------

radialQuaternion :
  _ → _ → _ → _ → _ → Quaternion
radialQuaternion c s u1 u2 u3 =
  quat c (s *R u1) (s *R u2) (s *R u3)

radialChordPolynomial : ∀ c s u1 u2 u3 →
  chordSquaredQ (radialQuaternion c s u1 u2 u3) oneQ
  ≡ ((c +R (-R oneR)) *R (c +R (-R oneR)))
    +R ((s *R s) *R
      (((u1 *R u1) +R (u2 *R u2)) +R (u3 *R u3)))
radialChordPolynomial =
  solveComputed 5
    (λ c s u1 u2 u3 →
      ((c :+ (:- con (RealPolynomialSolver.coefficient oneR)))
        :* (c :+ (:- con (RealPolynomialSolver.coefficient oneR))))
      :+ ((s :* s) :*
        (((u1 :* u1) :+ (u2 :* u2)) :+ (u3 :* u3)))
      :=
      ((c :+ (:- con (RealPolynomialSolver.coefficient oneR)))
        :* (c :+ (:- con (RealPolynomialSolver.coefficient oneR))))
      :+ ((s :* s) :*
        (((u1 :* u1) :+ (u2 :* u2)) :+ (u3 :* u3))))
    computed

record RadialUnitData (c s u1 u2 u3 : _) : Set where
  field
    directionUnit :
      (((u1 *R u1) +R (u2 *R u2)) +R (u3 *R u3)) ≡ oneR
    trigonometricUnit :
      (c *R c) +R (s *R s) ≡ oneR

open RadialUnitData public

radialChordSquaredIsTwoOneMinusCosine :
  ∀ c s u1 u2 u3 →
  RadialUnitData c s u1 u2 u3 →
  chordSquaredQ (radialQuaternion c s u1 u2 u3) oneQ
  ≡ (oneR +R oneR) *R (oneR +R (-R c))
radialChordSquaredIsTwoOneMinusCosine
    c s u1 u2 u3 radial =
  trans
    (radialChordPolynomial c s u1 u2 u3)
    (trans
      (cong
        (λ directionNorm →
          ((c +R (-R oneR)) *R (c +R (-R oneR)))
          +R ((s *R s) *R directionNorm))
        (directionUnit radial))
      (solveComputed 2
        (λ c s →
          ((c :+ (:- con (RealPolynomialSolver.coefficient oneR)))
            :* (c :+ (:- con (RealPolynomialSolver.coefficient oneR))))
          :+ ((s :* s) :* con (RealPolynomialSolver.coefficient oneR))
          :=
          (con (RealPolynomialSolver.coefficient oneR)
            :+ con (RealPolynomialSolver.coefficient oneR))
          :* (con (RealPolynomialSolver.coefficient oneR) :+ (:- c)))
        computed c s))

quaternionChordTransportPolynomialLevel : ProofLevel
quaternionChordTransportPolynomialLevel = machineChecked

su2ChordSquaredBiInvarianceLevel : ProofLevel
su2ChordSquaredBiInvarianceLevel = machineChecked

su2RadialChordFormulaLevel : ProofLevel
su2RadialChordFormulaLevel = machineChecked

chordSquareRootMetricCompletionLevel : ProofLevel
chordSquareRootMetricCompletionLevel = conditional
