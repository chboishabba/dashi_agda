module DASHI.Physics.YangMills.BalabanQuaternionNormPolynomialIdentity where

------------------------------------------------------------------------
-- Integer-coefficient proof of multiplicativity of the quaternion norm.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanRealPolynomialRing using
  ( _+R_; _*R_ )
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  ( module RealPolynomialSolver )
open RealPolynomialSolver using
  ( Polynomial; solve; _:=_; _:+_; _:*_ )
open import DASHI.Physics.YangMills.BalabanQuaternionPolynomialIdentities using
  ( q0R; q1R; q2R; q3R
  ; q0P; q1P; q2P; q3P
  )

normR : ℝ → ℝ → ℝ → ℝ → ℝ
normR a0 a1 a2 a3 =
  (((a0 *R a0) +R (a1 *R a1))
    +R (a2 *R a2)
    +R (a3 *R a3))

normP : ∀ {n : Nat} →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n →
  Polynomial n
normP a0 a1 a2 a3 =
  (((a0 :* a0) :+ (a1 :* a1))
    :+ (a2 :* a2)
    :+ (a3 :* a3))

quaternionNormMultiplicativePolynomial :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  normR
    (q0R a0 a1 a2 a3 b0 b1 b2 b3)
    (q1R a0 a1 a2 a3 b0 b1 b2 b3)
    (q2R a0 a1 a2 a3 b0 b1 b2 b3)
    (q3R a0 a1 a2 a3 b0 b1 b2 b3)
  ≡ normR a0 a1 a2 a3 *R normR b0 b1 b2 b3
quaternionNormMultiplicativePolynomial =
  solve 8
    (λ a0 a1 a2 a3 b0 b1 b2 b3 →
      normP
        (q0P a0 a1 a2 a3 b0 b1 b2 b3)
        (q1P a0 a1 a2 a3 b0 b1 b2 b3)
        (q2P a0 a1 a2 a3 b0 b1 b2 b3)
        (q3P a0 a1 a2 a3 b0 b1 b2 b3)
      :=
      normP a0 a1 a2 a3 :* normP b0 b1 b2 b3)
    refl
