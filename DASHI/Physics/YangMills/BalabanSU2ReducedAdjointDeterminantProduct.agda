module DASHI.Physics.YangMills.BalabanSU2ReducedAdjointDeterminantProduct where

------------------------------------------------------------------------
-- Determinant product law in the reduced su(2) adjoint algebra.
--
-- The concrete 3 x 3 determinant from
-- `BalabanSU2AdjointMatrixDeterminant` is multiplicative under the exact
-- reduced composition law.  This is the first literal determinant-product
-- theorem in the source-operator lane; it is finite algebra and contains no
-- logarithm, positivity, or beta estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

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

reducedAdjointDeterminantValue :
  SU2LieAlgebra → ReducedAdjointOperator → ℝ
reducedAdjointDeterminantValue Y operator =
  identityCoefficient operator *R
    (((identityCoefficient operator
        +R (quadraticCoefficient operator *R adCubicCoefficient Y))
       *R
       (identityCoefficient operator
        +R (quadraticCoefficient operator *R adCubicCoefficient Y)))
      +R
      (-R (adCubicCoefficient Y *R
        (linearCoefficient operator *R linearCoefficient operator))))

reducedAdjointMatrixDeterminantValue :
  ∀ Y operator →
  determinantMatrix3 (reducedAdjointMatrix Y operator)
    ≡ reducedAdjointDeterminantValue Y operator
reducedAdjointMatrixDeterminantValue
  Y (reducedAd a b c) =
  reducedAdjointDeterminant Y a b c

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
  Solver.solve
    (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ adCubicCoefficient Y ∷ [])
    realSolverRing

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
      (DASHI.Foundations.RealAnalysisAxioms.cong₂ _*R_
        (sym (reducedAdjointMatrixDeterminantValue Y left))
        (sym (reducedAdjointMatrixDeterminantValue Y right))))
