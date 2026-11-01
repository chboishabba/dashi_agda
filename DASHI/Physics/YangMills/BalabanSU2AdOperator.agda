module DASHI.Physics.YangMills.BalabanSU2AdOperator where

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using ([]; _∷_)
import Tactic.RingSolver as Solver

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (_+R_; _*R_; -R_; oneR; realSolverRing)
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (SU2LieAlgebra; su2Lie; su2LieExt; lieAdd; lieScale)
open import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct using
  (su2Dot)
open import DASHI.Physics.YangMills.BalabanSU2LieBracket using
  (twoR; lieBracket; adOperator)

lieNormSquared : SU2LieAlgebra → ℝ
lieNormSquared X = su2Dot X X

fourR : ℝ
fourR = twoR *R twoR

cAd : ℝ
cAd = fourR

adAdd :
  ∀ Y X Z →
  adOperator Y (lieAdd X Z)
    ≡ lieAdd (adOperator Y X) (adOperator Y Z)
adAdd
  (su2Lie x₀ y₀ z₀)
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂) =
  su2LieExt
    (Solver.solve
      (x₀ ∷ y₀ ∷ z₀ ∷ x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)
    (Solver.solve
      (x₀ ∷ y₀ ∷ z₀ ∷ x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)
    (Solver.solve
      (x₀ ∷ y₀ ∷ z₀ ∷ x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)

adScale :
  ∀ Y scalar X →
  adOperator Y (lieScale scalar X)
    ≡ lieScale scalar (adOperator Y X)
adScale
  (su2Lie x₀ y₀ z₀) scalar (su2Lie x y z) =
  su2LieExt
    (Solver.solve (x₀ ∷ y₀ ∷ z₀ ∷ scalar ∷ x ∷ y ∷ z ∷ []) realSolverRing)
    (Solver.solve (x₀ ∷ y₀ ∷ z₀ ∷ scalar ∷ x ∷ y ∷ z ∷ []) realSolverRing)
    (Solver.solve (x₀ ∷ y₀ ∷ z₀ ∷ scalar ∷ x ∷ y ∷ z ∷ []) realSolverRing)

-- With [X,Y] = 2 X×Y, ad_Y^3 = -4 |Y|² ad_Y.
adCubic :
  ∀ Y X →
  adOperator Y (adOperator Y (adOperator Y X))
    ≡ lieScale
        (-R (cAd *R lieNormSquared Y))
        (adOperator Y X)
adCubic
  (su2Lie x₀ y₀ z₀)
  (su2Lie x y z) =
  su2LieExt
    (Solver.solve (x₀ ∷ y₀ ∷ z₀ ∷ x ∷ y ∷ z ∷ []) realSolverRing)
    (Solver.solve (x₀ ∷ y₀ ∷ z₀ ∷ x ∷ y ∷ z ∷ []) realSolverRing)
    (Solver.solve (x₀ ∷ y₀ ∷ z₀ ∷ x ∷ y ∷ z ∷ []) realSolverRing)
