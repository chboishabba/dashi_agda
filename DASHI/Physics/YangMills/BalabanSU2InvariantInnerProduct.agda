module DASHI.Physics.YangMills.BalabanSU2InvariantInnerProduct where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  ( module RealPolynomialSolver )
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  ( solveComputed; computed )
open RealPolynomialSolver using (_:=_; _:+_)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (_+R_; -R_)
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (SU2LieAlgebra; su2Lie; lieAdd; su2Adjoint)
open import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct using
  (su2Dot; su2DotAdjointInvariant; su2AdjointInnerProductModule)
open import DASHI.Physics.YangMills.BalabanSU2LieBracket using
  (lieBracket; lieBracketSkewAdjoint; dotP)

lieInnerProduct : SU2LieAlgebra → SU2LieAlgebra → ℝ
lieInnerProduct = su2Dot

lieNormSquared : SU2LieAlgebra → ℝ
lieNormSquared X = lieInnerProduct X X

innerSymmetric :
  ∀ X Y → lieInnerProduct X Y ≡ lieInnerProduct Y X
innerSymmetric (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  solveComputed 6
    (λ x₁ y₁ z₁ x₂ y₂ z₂ →
      dotP x₁ y₁ z₁ x₂ y₂ z₂ := dotP x₂ y₂ z₂ x₁ y₁ z₁)
    computed x₁ y₁ z₁ x₂ y₂ z₂

innerAddLeft :
  ∀ X Y Z →
  lieInnerProduct (lieAdd X Y) Z
    ≡ lieInnerProduct X Z +R lieInnerProduct Y Z
innerAddLeft
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂)
  (su2Lie x₃ y₃ z₃) =
  solveComputed 9
    (λ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
      dotP (x₁ :+ x₂) (y₁ :+ y₂) (z₁ :+ z₂) x₃ y₃ z₃ :=
      dotP x₁ y₁ z₁ x₃ y₃ z₃ :+ dotP x₂ y₂ z₂ x₃ y₃ z₃)
    computed x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃

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
