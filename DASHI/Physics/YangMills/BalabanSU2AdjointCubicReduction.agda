module DASHI.Physics.YangMills.BalabanSU2AdjointCubicReduction where

------------------------------------------------------------------------
-- Exact cubic reduction for the concrete su(2) adjoint operator.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (suc)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  ( module RealPolynomialSolver )
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  ( solveComputed; computed )
open RealPolynomialSolver using
  ( Polynomial; _:=_; _:+_; _:*_; :-_ )
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( _+R_
  ; _*R_
  ; -R_
  ; oneR
  )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra
  ; su2Lie
  ; su2LieExt
  ; lieScale
  ; xComponent
  ; yComponent
  ; zComponent
  )
open import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct using
  ( su2Dot )
open import DASHI.Physics.YangMills.BalabanSU2LieBracket using
  ( adOperator
  ; bracket1P
  ; bracket2P
  ; bracket3P
  ; dotP
  ; twoP
  )
open import DASHI.Physics.YangMills.BalabanSU2AdjointPolynomialCalculus using
  ( adPower )

twoR : ℝ
twoR = oneR +R oneR

fourR : ℝ
fourR = twoR *R twoR

fourP : ∀ {n} → Polynomial n
fourP = twoP :* twoP

adCubicCoefficient : SU2LieAlgebra → ℝ
adCubicCoefficient Y = -R (fourR *R su2Dot Y Y)

ad1P : ∀ {n} →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
ad1P y₁ y₂ y₃ x₁ x₂ x₃ = bracket1P y₂ y₃ x₂ x₃

ad2P : ∀ {n} →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
ad2P y₁ y₂ y₃ x₁ x₂ x₃ = bracket2P y₃ y₁ x₃ x₁

ad3P : ∀ {n} →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
ad3P y₁ y₂ y₃ x₁ x₂ x₃ = bracket3P y₁ y₂ x₁ x₂

adSquare1P : ∀ {n} →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
adSquare1P y₁ y₂ y₃ x₁ x₂ x₃ =
  bracket1P y₂ y₃
    (ad2P y₁ y₂ y₃ x₁ x₂ x₃)
    (ad3P y₁ y₂ y₃ x₁ x₂ x₃)

adSquare2P : ∀ {n} →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
adSquare2P y₁ y₂ y₃ x₁ x₂ x₃ =
  bracket2P y₃ y₁
    (ad3P y₁ y₂ y₃ x₁ x₂ x₃)
    (ad1P y₁ y₂ y₃ x₁ x₂ x₃)

adSquare3P : ∀ {n} →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
adSquare3P y₁ y₂ y₃ x₁ x₂ x₃ =
  bracket3P y₁ y₂
    (ad1P y₁ y₂ y₃ x₁ x₂ x₃)
    (ad2P y₁ y₂ y₃ x₁ x₂ x₃)

adSquareVectorIdentity :
  ∀ Y X →
  adOperator Y (adOperator Y X)
  ≡
  su2Lie
    (fourR *R
      ((su2Dot Y X *R xComponent Y)
        +R (-R (su2Dot Y Y *R xComponent X))))
    (fourR *R
      ((su2Dot Y X *R yComponent Y)
        +R (-R (su2Dot Y Y *R yComponent X))))
    (fourR *R
      ((su2Dot Y X *R zComponent Y)
        +R (-R (su2Dot Y Y *R zComponent X))))
adSquareVectorIdentity
  (su2Lie y₁ y₂ y₃)
  (su2Lie x₁ x₂ x₃) =
  su2LieExt
    (solveComputed 6
      (λ y₁ y₂ y₃ x₁ x₂ x₃ →
        adSquare1P y₁ y₂ y₃ x₁ x₂ x₃ :=
        fourP :* ((dotP y₁ y₂ y₃ x₁ x₂ x₃ :* y₁)
          :+ (:- (dotP y₁ y₂ y₃ y₁ y₂ y₃ :* x₁))))
      computed)
    (solveComputed 6
      (λ y₁ y₂ y₃ x₁ x₂ x₃ →
        adSquare2P y₁ y₂ y₃ x₁ x₂ x₃ :=
        fourP :* ((dotP y₁ y₂ y₃ x₁ x₂ x₃ :* y₂)
          :+ (:- (dotP y₁ y₂ y₃ y₁ y₂ y₃ :* x₂))))
      computed)
    (solveComputed 6
      (λ y₁ y₂ y₃ x₁ x₂ x₃ →
        adSquare3P y₁ y₂ y₃ x₁ x₂ x₃ :=
        fourP :* ((dotP y₁ y₂ y₃ x₁ x₂ x₃ :* y₃)
          :+ (:- (dotP y₁ y₂ y₃ y₁ y₂ y₃ :* x₃))))
      computed)

adCubicReduction :
  ∀ Y X →
  adOperator Y (adOperator Y (adOperator Y X))
    ≡ lieScale (adCubicCoefficient Y) (adOperator Y X)
adCubicReduction
  (su2Lie y₁ y₂ y₃)
  (su2Lie x₁ x₂ x₃) =
  su2LieExt
    (solveComputed 6
      (λ y₁ y₂ y₃ x₁ x₂ x₃ →
        bracket1P y₂ y₃
          (adSquare2P y₁ y₂ y₃ x₁ x₂ x₃)
          (adSquare3P y₁ y₂ y₃ x₁ x₂ x₃)
        :=
        (:- (fourP :* (dotP y₁ y₂ y₃ y₁ y₂ y₃))) :*
          ad1P y₁ y₂ y₃ x₁ x₂ x₃)
      computed)
    (solveComputed 6
      (λ y₁ y₂ y₃ x₁ x₂ x₃ →
        bracket2P y₃ y₁
          (adSquare3P y₁ y₂ y₃ x₁ x₂ x₃)
          (adSquare1P y₁ y₂ y₃ x₁ x₂ x₃)
        :=
        (:- (fourP :* (dotP y₁ y₂ y₃ y₁ y₂ y₃))) :*
          ad2P y₁ y₂ y₃ x₁ x₂ x₃)
      computed)
    (solveComputed 6
      (λ y₁ y₂ y₃ x₁ x₂ x₃ →
        bracket3P y₁ y₂
          (adSquare1P y₁ y₂ y₃ x₁ x₂ x₃)
          (adSquare2P y₁ y₂ y₃ x₁ x₂ x₃)
        :=
        (:- (fourP :* (dotP y₁ y₂ y₃ y₁ y₂ y₃))) :*
          ad3P y₁ y₂ y₃ x₁ x₂ x₃)
      computed)

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
