module DASHI.Physics.YangMills.BalabanSU2ReducedAdjointDeterminantProduct where

------------------------------------------------------------------------
-- Determinant product law in the reduced su(2) adjoint algebra.
--
-- The determinant and reduced composition are exposed below as explicit
-- polynomial syntax.  This keeps the concrete coefficient k as a genuine
-- solver variable and avoids treating local helper applications as opaque
-- constants in the reflective ring tactic.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  ( module RealPolynomialSolver )
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  ( solveComputed; computed )
open RealPolynomialSolver using
  ( Polynomial
  ; _:=_
  ; _:+_
  ; _:*_
  ; :-_
  )
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( _+R_
  ; _*R_
  ; -R_
  )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra )
open import DASHI.Physics.YangMills.BalabanSU2AdjointCubicReduction using
  ( adCubicCoefficient )
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus using
  ( ReducedAdjointOperator
  ; reducedAd
  ; identityCoefficient
  ; linearCoefficient
  ; quadraticCoefficient
  ; composeReducedAdjoint
  ; composeAP
  ; composeBP
  ; composeCP
  )
open import DASHI.Physics.YangMills.BalabanSU2AdjointMatrixDeterminant using
  ( determinantMatrix3
  ; reducedAdjointMatrix
  ; reducedAdjointDeterminant
  )

reducedAdjointDeterminantValueAt :
  ℝ → ReducedAdjointOperator → ℝ
reducedAdjointDeterminantValueAt k operator =
  identityCoefficient operator *R
    (((identityCoefficient operator
        +R (quadraticCoefficient operator *R k))
       *R
       (identityCoefficient operator
        +R (quadraticCoefficient operator *R k)))
      +R
      (-R (k *R
        (linearCoefficient operator *R linearCoefficient operator))))

composeReducedAdjointAt :
  ℝ → ReducedAdjointOperator → ReducedAdjointOperator → ReducedAdjointOperator
composeReducedAdjointAt k (reducedAd a b c) (reducedAd d e f) =
  reducedAd
    (a *R d)
    (((a *R e) +R (b *R d)) +R (k *R ((b *R f) +R (c *R e))))
    ((((a *R f) +R (b *R e)) +R (c *R d)) +R (k *R (c *R f)))

reducedAdjointDeterminantValueP :
  ∀ {n} →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
reducedAdjointDeterminantValueP k a b c =
  a :*
    (((a :+ (c :* k)) :* (a :+ (c :* k)))
      :+ (:- (k :* (b :* b))))

reducedAdjointDeterminantValue :
  SU2LieAlgebra → ReducedAdjointOperator → ℝ
reducedAdjointDeterminantValue Y =
  reducedAdjointDeterminantValueAt (adCubicCoefficient Y)

reducedAdjointMatrixDeterminantValue :
  ∀ Y operator →
  determinantMatrix3 (reducedAdjointMatrix Y operator)
    ≡ reducedAdjointDeterminantValue Y operator
reducedAdjointMatrixDeterminantValue
  Y (reducedAd a b c) =
  reducedAdjointDeterminant Y a b c

reducedAdjointDeterminantMultiplicativeAt :
  ∀ k a b c d e f →
  reducedAdjointDeterminantValueAt k
    (composeReducedAdjointAt k (reducedAd a b c) (reducedAd d e f))
  ≡
  reducedAdjointDeterminantValueAt k (reducedAd a b c)
    *R reducedAdjointDeterminantValueAt k (reducedAd d e f)
reducedAdjointDeterminantMultiplicativeAt k a b c d e f =
  solveComputed 7
    (λ a b c d e f k →
      reducedAdjointDeterminantValueP k
        (composeAP a d)
        (composeBP k a b c d e f)
        (composeCP k a b c d e f)
      :=
      (reducedAdjointDeterminantValueP k a b c
        :* reducedAdjointDeterminantValueP k d e f))
    computed a b c d e f k

reducedAdjointDeterminantMultiplicative :
  ∀ Y left right →
  reducedAdjointDeterminantValue Y
    (composeReducedAdjoint Y left right)
  ≡
  reducedAdjointDeterminantValue Y left
    *R reducedAdjointDeterminantValue Y right
reducedAdjointDeterminantMultiplicative Y
  (reducedAd a b c)
  (reducedAd d e f) =
  reducedAdjointDeterminantMultiplicativeAt
    (adCubicCoefficient Y) a b c d e f

reducedAdjointMatrixDeterminantMultiplicative :
  ∀ Y left right →
  determinantMatrix3
    (reducedAdjointMatrix Y
      (composeReducedAdjoint Y left right))
  ≡
  determinantMatrix3 (reducedAdjointMatrix Y left)
    *R determinantMatrix3 (reducedAdjointMatrix Y right)
reducedAdjointMatrixDeterminantMultiplicative Y left right =
  trans
    (reducedAdjointMatrixDeterminantValue Y
      (composeReducedAdjoint Y left right))
    (trans
      (reducedAdjointDeterminantMultiplicative Y left right)
      (cong₂ _*R_
        (sym (reducedAdjointMatrixDeterminantValue Y left))
        (sym (reducedAdjointMatrixDeterminantValue Y right))))
