module DASHI.Physics.YangMills.BalabanSU2AdjointCubicReduction where

------------------------------------------------------------------------
-- Exact cubic reduction for the concrete su(2) adjoint operator.
--
-- With the quaternion convention used here,
--
--   [Y,X] = 2 Y cross X.
--
-- Hence
--
--   ad_Y^2 X = 4 ((Y dot X)Y - (Y dot Y)X)
--   ad_Y^3 X = -4 (Y dot Y) ad_Y X.
--
-- This is the finite-dimensional algebraic reason every analytic function of
-- `ad_Y` reduces to a combination of I, ad_Y, and ad_Y^2.  The scalar analytic
-- coefficient functions are not introduced here; only the exact polynomial
-- identity is proved.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using ([]; _∷_)

import Tactic.RingSolver as Solver

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( _+R_
  ; _*R_
  ; -R_
  ; oneR
  ; realSolverRing
  )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra
  ; su2Lie
  ; su2LieExt
  ; lieScale
  )
open import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct using
  ( su2Dot )
open import DASHI.Physics.YangMills.BalabanSU2LieBracket using
  ( adOperator )
open import DASHI.Physics.YangMills.BalabanSU2AdjointPolynomialCalculus using
  ( adPower )

twoR : ℝ
twoR = oneR +R oneR

fourR : ℝ
fourR = twoR *R twoR

adCubicCoefficient : SU2LieAlgebra → ℝ
adCubicCoefficient Y = -R (fourR *R su2Dot Y Y)

adSquareVectorIdentity :
  ∀ Y X →
  adOperator Y (adOperator Y X)
  ≡
  su2Lie
    (fourR *R
      ((su2Dot Y X *R DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier.xComponent Y)
        +R (-R (su2Dot Y Y *R DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier.xComponent X))))
    (fourR *R
      ((su2Dot Y X *R DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier.yComponent Y)
        +R (-R (su2Dot Y Y *R DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier.yComponent X))))
    (fourR *R
      ((su2Dot Y X *R DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier.zComponent Y)
        +R (-R (su2Dot Y Y *R DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier.zComponent X))))
adSquareVectorIdentity
  (su2Lie y₁ y₂ y₃)
  (su2Lie x₁ x₂ x₃) =
  su2LieExt
    (Solver.solve
      (y₁ ∷ y₂ ∷ y₃ ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (y₁ ∷ y₂ ∷ y₃ ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (y₁ ∷ y₂ ∷ y₃ ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])
      realSolverRing)

adCubicReduction :
  ∀ Y X →
  adOperator Y (adOperator Y (adOperator Y X))
    ≡ lieScale (adCubicCoefficient Y) (adOperator Y X)
adCubicReduction
  (su2Lie y₁ y₂ y₃)
  (su2Lie x₁ x₂ x₃) =
  su2LieExt
    (Solver.solve
      (y₁ ∷ y₂ ∷ y₃ ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (y₁ ∷ y₂ ∷ y₃ ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (y₁ ∷ y₂ ∷ y₃ ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])
      realSolverRing)

adPowerCubicRecurrence :
  ∀ n Y X →
  adPower (suc (suc (suc n))) Y X
    ≡ lieScale
        (adCubicCoefficient Y)
        (adPower (suc n) Y X)
adPowerCubicRecurrence n Y X =
  adCubicReduction Y (adPower n Y X)

adFourthReduction :
  ∀ Y X →
  adOperator Y
    (adOperator Y (adOperator Y (adOperator Y X)))
  ≡
  lieScale
    (adCubicCoefficient Y)
    (adOperator Y (adOperator Y X))
adFourthReduction Y X =
  adCubicReduction Y (adOperator Y X)
