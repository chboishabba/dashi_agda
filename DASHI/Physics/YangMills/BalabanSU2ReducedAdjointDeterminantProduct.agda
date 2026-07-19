module DASHI.Physics.YangMills.BalabanSU2ReducedAdjointDeterminantProduct where

------------------------------------------------------------------------
-- Determinant product law in the reduced su(2) adjoint algebra.
--
-- The reflective solver must receive variables, not a composite expression.
-- We therefore prove the polynomial identity for an explicit scalar k and only
-- then instantiate k with the concrete cubic coefficient of ad(Y).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import Tactic.RingSolver as Solver

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( _+R_
  ; _*R_
  ; -R_
  ; realSolverRing
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
  Solver.solve
    (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ k ∷ [])
    realSolverRing

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
