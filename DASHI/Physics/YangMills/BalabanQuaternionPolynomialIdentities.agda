module DASHI.Physics.YangMills.BalabanQuaternionPolynomialIdentities where

------------------------------------------------------------------------
-- Solver-normalised scalar identities behind quaternion multiplication.
--
-- This module is intentionally independent of the quaternion record.  It
-- states the four component formulae over DASHI's real carrier and proves
-- their associativity using the separate integer-coefficient solver socket.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanRealPolynomialRing using
  ( _+R_; _*R_; -R_; zeroR )
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  ( module RealPolynomialSolver
  ; IntegerCoefficient
  ; coefficient
  )
open RealPolynomialSolver using
  ( Polynomial; solve; _:=_; _:+_; _:*_; :-_ )
open RealPolynomialSolver using (con)
zeroPolynomial : ∀ {n : Nat} → Polynomial n
zeroPolynomial = con (coefficient zero zero)

q0R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
q0R a0 a1 a2 a3 b0 b1 b2 b3 =
  (((a0 *R b0) +R (-R (a1 *R b1)))
    +R (-R (a2 *R b2))
    +R (-R (a3 *R b3)))

q1R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
q1R a0 a1 a2 a3 b0 b1 b2 b3 =
  (((a0 *R b1) +R (a1 *R b0))
    +R (a2 *R b3)
    +R (-R (a3 *R b2)))

q2R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
q2R a0 a1 a2 a3 b0 b1 b2 b3 =
  (((a0 *R b2) +R (-R (a1 *R b3)))
    +R (a2 *R b0)
    +R (a3 *R b1))

q3R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
q3R a0 a1 a2 a3 b0 b1 b2 b3 =
  (((a0 *R b3) +R (a1 *R b2))
    +R (-R (a2 *R b1))
    +R (a3 *R b0))

q0P : ∀ {n : Nat} →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n →
  Polynomial n
q0P a0 a1 a2 a3 b0 b1 b2 b3 =
  (((a0 :* b0) :+ (:- (a1 :* b1)))
    :+ (:- (a2 :* b2))
    :+ (:- (a3 :* b3)))

q1P : ∀ {n : Nat} →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n →
  Polynomial n
q1P a0 a1 a2 a3 b0 b1 b2 b3 =
  (((a0 :* b1) :+ (a1 :* b0))
    :+ (a2 :* b3)
    :+ (:- (a3 :* b2)))

q2P : ∀ {n : Nat} →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n →
  Polynomial n
q2P a0 a1 a2 a3 b0 b1 b2 b3 =
  (((a0 :* b2) :+ (:- (a1 :* b3)))
    :+ (a2 :* b0)
    :+ (a3 :* b1))

q3P : ∀ {n : Nat} →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n →
  Polynomial n
q3P a0 a1 a2 a3 b0 b1 b2 b3 =
  (((a0 :* b3) :+ (a1 :* b2))
    :+ (:- (a2 :* b1))
    :+ (a3 :* b0))

quaternionAssoc0Polynomial :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
  q0R
    (q0R a0 a1 a2 a3 b0 b1 b2 b3)
    (q1R a0 a1 a2 a3 b0 b1 b2 b3)
    (q2R a0 a1 a2 a3 b0 b1 b2 b3)
    (q3R a0 a1 a2 a3 b0 b1 b2 b3)
    c0 c1 c2 c3
  ≡
  q0R a0 a1 a2 a3
    (q0R b0 b1 b2 b3 c0 c1 c2 c3)
    (q1R b0 b1 b2 b3 c0 c1 c2 c3)
    (q2R b0 b1 b2 b3 c0 c1 c2 c3)
    (q3R b0 b1 b2 b3 c0 c1 c2 c3)
quaternionAssoc0Polynomial =
  solve 12
    (λ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
      q0P
        (q0P a0 a1 a2 a3 b0 b1 b2 b3)
        (q1P a0 a1 a2 a3 b0 b1 b2 b3)
        (q2P a0 a1 a2 a3 b0 b1 b2 b3)
        (q3P a0 a1 a2 a3 b0 b1 b2 b3)
        c0 c1 c2 c3
      :=
      q0P a0 a1 a2 a3
        (q0P b0 b1 b2 b3 c0 c1 c2 c3)
        (q1P b0 b1 b2 b3 c0 c1 c2 c3)
        (q2P b0 b1 b2 b3 c0 c1 c2 c3)
        (q3P b0 b1 b2 b3 c0 c1 c2 c3))
    refl

quaternionAssoc1Polynomial :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
  q1R
    (q0R a0 a1 a2 a3 b0 b1 b2 b3)
    (q1R a0 a1 a2 a3 b0 b1 b2 b3)
    (q2R a0 a1 a2 a3 b0 b1 b2 b3)
    (q3R a0 a1 a2 a3 b0 b1 b2 b3)
    c0 c1 c2 c3
  ≡
  q1R a0 a1 a2 a3
    (q0R b0 b1 b2 b3 c0 c1 c2 c3)
    (q1R b0 b1 b2 b3 c0 c1 c2 c3)
    (q2R b0 b1 b2 b3 c0 c1 c2 c3)
    (q3R b0 b1 b2 b3 c0 c1 c2 c3)
quaternionAssoc1Polynomial =
  solve 12
    (λ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
      q1P
        (q0P a0 a1 a2 a3 b0 b1 b2 b3)
        (q1P a0 a1 a2 a3 b0 b1 b2 b3)
        (q2P a0 a1 a2 a3 b0 b1 b2 b3)
        (q3P a0 a1 a2 a3 b0 b1 b2 b3)
        c0 c1 c2 c3
      :=
      q1P a0 a1 a2 a3
        (q0P b0 b1 b2 b3 c0 c1 c2 c3)
        (q1P b0 b1 b2 b3 c0 c1 c2 c3)
        (q2P b0 b1 b2 b3 c0 c1 c2 c3)
        (q3P b0 b1 b2 b3 c0 c1 c2 c3))
    refl

quaternionAssoc2Polynomial :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
  q2R
    (q0R a0 a1 a2 a3 b0 b1 b2 b3)
    (q1R a0 a1 a2 a3 b0 b1 b2 b3)
    (q2R a0 a1 a2 a3 b0 b1 b2 b3)
    (q3R a0 a1 a2 a3 b0 b1 b2 b3)
    c0 c1 c2 c3
  ≡
  q2R a0 a1 a2 a3
    (q0R b0 b1 b2 b3 c0 c1 c2 c3)
    (q1R b0 b1 b2 b3 c0 c1 c2 c3)
    (q2R b0 b1 b2 b3 c0 c1 c2 c3)
    (q3R b0 b1 b2 b3 c0 c1 c2 c3)
quaternionAssoc2Polynomial =
  solve 12
    (λ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
      q2P
        (q0P a0 a1 a2 a3 b0 b1 b2 b3)
        (q1P a0 a1 a2 a3 b0 b1 b2 b3)
        (q2P a0 a1 a2 a3 b0 b1 b2 b3)
        (q3P a0 a1 a2 a3 b0 b1 b2 b3)
        c0 c1 c2 c3
      :=
      q2P a0 a1 a2 a3
        (q0P b0 b1 b2 b3 c0 c1 c2 c3)
        (q1P b0 b1 b2 b3 c0 c1 c2 c3)
        (q2P b0 b1 b2 b3 c0 c1 c2 c3)
        (q3P b0 b1 b2 b3 c0 c1 c2 c3))
    refl

quaternionAssoc3Polynomial :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
  q3R
    (q0R a0 a1 a2 a3 b0 b1 b2 b3)
    (q1R a0 a1 a2 a3 b0 b1 b2 b3)
    (q2R a0 a1 a2 a3 b0 b1 b2 b3)
    (q3R a0 a1 a2 a3 b0 b1 b2 b3)
    c0 c1 c2 c3
  ≡
  q3R a0 a1 a2 a3
    (q0R b0 b1 b2 b3 c0 c1 c2 c3)
    (q1R b0 b1 b2 b3 c0 c1 c2 c3)
    (q2R b0 b1 b2 b3 c0 c1 c2 c3)
    (q3R b0 b1 b2 b3 c0 c1 c2 c3)
quaternionAssoc3Polynomial =
  solve 12
    (λ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
      q3P
        (q0P a0 a1 a2 a3 b0 b1 b2 b3)
        (q1P a0 a1 a2 a3 b0 b1 b2 b3)
        (q2P a0 a1 a2 a3 b0 b1 b2 b3)
        (q3P a0 a1 a2 a3 b0 b1 b2 b3)
        c0 c1 c2 c3
      :=
      q3P a0 a1 a2 a3
        (q0P b0 b1 b2 b3 c0 c1 c2 c3)
        (q1P b0 b1 b2 b3 c0 c1 c2 c3)
        (q2P b0 b1 b2 b3 c0 c1 c2 c3)
        (q3P b0 b1 b2 b3 c0 c1 c2 c3))
    refl

quaternionConjugateRight1Polynomial :
  ∀ a0 a1 a2 a3 →
  (((a0 *R (-R a1)) +R (a1 *R a0))
    +R (a2 *R (-R a3))
    +R (-R (a3 *R (-R a2))))
  ≡
  (a0 *R (-R a1)) +R (-R (a0 *R (-R a1)))
quaternionConjugateRight1Polynomial =
  solve 4
    (λ a0 a1 a2 a3 →
      (((a0 :* (:- a1)) :+ (a1 :* a0))
        :+ (a2 :* (:- a3))
        :+ (:- (a3 :* (:- a2))))
      :=
      ((a0 :* (:- a1)) :+ (:- (a0 :* (:- a1)))))
    refl

quaternionConjugateRight2Polynomial :
  ∀ a0 a1 a2 a3 →
  (((a0 *R (-R a2)) +R (-R (a1 *R (-R a3)))
    +R (a2 *R a0))
    +R (a3 *R (-R a1)))
  ≡
  (a0 *R (-R a2)) +R (-R (a0 *R (-R a2)))
quaternionConjugateRight2Polynomial =
  solve 4
    (λ a0 a1 a2 a3 →
      (((a0 :* (:- a2)) :+ (:- (a1 :* (:- a3))))
        :+ (a2 :* a0)
        :+ (a3 :* (:- a1)))
      :=
      ((a0 :* (:- a2)) :+ (:- (a0 :* (:- a2)))))
    refl

quaternionConjugateRight3Polynomial :
  ∀ a0 a1 a2 a3 →
  (((a0 *R (-R a3)) +R (a1 *R (-R a2))
    +R (-R (a2 *R (-R a1))))
    +R (a3 *R a0))
  ≡
  (a0 *R (-R a3)) +R (-R (a0 *R (-R a3)))
quaternionConjugateRight3Polynomial =
  solve 4
    (λ a0 a1 a2 a3 →
      (((a0 :* (:- a3)) :+ (a1 :* (:- a2)))
        :+ (:- (a2 :* (:- a1)))
        :+ (a3 :* a0))
      :=
      ((a0 :* (:- a3)) :+ (:- (a0 :* (:- a3)))))
    refl

quaternionPureImaginaryConjugation0Polynomial :
  ∀ a0 a1 a2 a3 x y z →
  q0R
    (q0R a0 a1 a2 a3 zeroR x y z)
    (q1R a0 a1 a2 a3 zeroR x y z)
    (q2R a0 a1 a2 a3 zeroR x y z)
    (q3R a0 a1 a2 a3 zeroR x y z)
    a0 (-R a1) (-R a2) (-R a3)
  ≡ zeroR
quaternionPureImaginaryConjugation0Polynomial =
  solve 7
    (λ a0 a1 a2 a3 x y z →
      q0P
        (q0P a0 a1 a2 a3 zeroPolynomial x y z)
        (q1P a0 a1 a2 a3 zeroPolynomial x y z)
        (q2P a0 a1 a2 a3 zeroPolynomial x y z)
        (q3P a0 a1 a2 a3 zeroPolynomial x y z)
        a0 (:- a1) (:- a2) (:- a3)
      := zeroPolynomial)
    refl
