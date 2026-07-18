module DASHI.Physics.YangMills.BalabanSU2InvariantInnerProduct where

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using ([]; _∷_)
import Tactic.RingSolver as Solver

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (_+R_; -R_; realSolverRing)
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (SU2LieAlgebra; su2Lie; lieAdd; su2Adjoint)
open import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct using
  (su2Dot; su2DotAdjointInvariant; su2AdjointInnerProductModule)
open import DASHI.Physics.YangMills.BalabanSU2LieBracket using
  (lieBracket; lieBracketSkewAdjoint)

lieInnerProduct : SU2LieAlgebra → SU2LieAlgebra → ℝ
lieInnerProduct = su2Dot

lieNormSquared : SU2LieAlgebra → ℝ
lieNormSquared X = lieInnerProduct X X

innerSymmetric :
  ∀ X Y → lieInnerProduct X Y ≡ lieInnerProduct Y X
innerSymmetric (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  Solver.solve
    (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ [])
    realSolverRing

innerAddLeft :
  ∀ X Y Z →
  lieInnerProduct (lieAdd X Y) Z
    ≡ lieInnerProduct X Z +R lieInnerProduct Y Z
innerAddLeft
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂)
  (su2Lie x₃ y₃ z₃) =
  Solver.solve
    (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ x₃ ∷ y₃ ∷ z₃ ∷ [])
    realSolverRing

adjointInnerInvariant :
  ∀ u X Y →
  lieInnerProduct (su2Adjoint u X) (su2Adjoint u Y)
    ≡ lieInnerProduct X Y
adjointInnerInvariant = su2DotAdjointInvariant

adSkewAdjoint :
  ∀ X Y Z →
  lieInnerProduct (lieBracket X Y) Z
    ≡ -R (lieInnerProduct Y (lieBracket X Z))
adSkewAdjoint = lieBracketSkewAdjoint
