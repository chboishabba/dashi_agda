module DASHI.Physics.YangMills.BalabanSU2LieBracket where

------------------------------------------------------------------------
-- Concrete su(2) Lie bracket.
--
-- For pure-imaginary quaternions the commutator is twice the cross product.
-- Every nontrivial component identity below is normalized through DASHI's
-- computable integer-coefficient polynomial socket.  This avoids relying on
-- definitional visibility of the axiomatic real aliases.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  ( module RealPolynomialSolver; zeroCoefficient; oneCoefficient )
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  ( solveComputed; computed )
open RealPolynomialSolver using
  ( Polynomial; con; _:=_; _:+_; _:*_; :-_ )
open import DASHI.Physics.YangMills.BalabanQuaternionPolynomialIdentities using
  ( q0P; q1P; q2P; q3P )
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( Quaternion
  ; quat
  ; q0
  ; q1
  ; q2
  ; q3
  ; _+R_
  ; _*R_
  ; -R_
  ; zeroR
  ; oneR
  ; _+q_
  ; negQ
  ; _*q_
  ; quaternionExt
  )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra
  ; su2Lie
  ; xComponent
  ; yComponent
  ; zComponent
  ; su2LieExt
  ; lieQuaternion
  ; lieAdd
  ; lieNegate
  ; lieScale
  )
open import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct using
  ( su2Dot )

zeroP : ∀ {n} → Polynomial n
zeroP = con zeroCoefficient

oneP : ∀ {n} → Polynomial n
oneP = con oneCoefficient

twoP : ∀ {n} → Polynomial n
twoP = oneP :+ oneP

twoR : ℝ
twoR = oneR +R oneR

bracket1R : ℝ → ℝ → ℝ → ℝ → ℝ
bracket1R y₁ z₁ y₂ z₂ =
  twoR *R ((y₁ *R z₂) +R (-R (z₁ *R y₂)))

bracket2R : ℝ → ℝ → ℝ → ℝ → ℝ
bracket2R z₁ x₁ z₂ x₂ =
  twoR *R ((z₁ *R x₂) +R (-R (x₁ *R z₂)))

bracket3R : ℝ → ℝ → ℝ → ℝ → ℝ
bracket3R x₁ y₁ x₂ y₂ =
  twoR *R ((x₁ *R y₂) +R (-R (y₁ *R x₂)))

bracket1P : ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
bracket1P y₁ z₁ y₂ z₂ = twoP :* ((y₁ :* z₂) :+ (:- (z₁ :* y₂)))

bracket2P : ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
bracket2P z₁ x₁ z₂ x₂ = twoP :* ((z₁ :* x₂) :+ (:- (x₁ :* z₂)))

bracket3P : ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
bracket3P x₁ y₁ x₂ y₂ = twoP :* ((x₁ :* y₂) :+ (:- (y₁ :* x₂)))

dotP : ∀ {n} →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
dotP x₁ y₁ z₁ x₂ y₂ z₂ =
  ((x₁ :* x₂) :+ (y₁ :* y₂)) :+ (z₁ :* z₂)

lieBracket : SU2LieAlgebra → SU2LieAlgebra → SU2LieAlgebra
lieBracket
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂) =
  su2Lie
    (bracket1R y₁ z₁ y₂ z₂)
    (bracket2R z₁ x₁ z₂ x₂)
    (bracket3R x₁ y₁ x₂ y₂)

lieBracketQuaternionCommutator :
  ∀ X Y →
  lieQuaternion (lieBracket X Y)
    ≡
  (lieQuaternion X *q lieQuaternion Y)
    +q negQ (lieQuaternion Y *q lieQuaternion X)
lieBracketQuaternionCommutator
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂) =
  quaternionExt
    (solveComputed 6
      (λ x₁ y₁ z₁ x₂ y₂ z₂ →
        zeroP :=
        q0P zeroP x₁ y₁ z₁ zeroP x₂ y₂ z₂
          :+ (:- q0P zeroP x₂ y₂ z₂ zeroP x₁ y₁ z₁))
      computed)
    (solveComputed 6
      (λ x₁ y₁ z₁ x₂ y₂ z₂ →
        bracket1P y₁ z₁ y₂ z₂ :=
        q1P zeroP x₁ y₁ z₁ zeroP x₂ y₂ z₂
          :+ (:- q1P zeroP x₂ y₂ z₂ zeroP x₁ y₁ z₁))
      computed)
    (solveComputed 6
      (λ x₁ y₁ z₁ x₂ y₂ z₂ →
        bracket2P z₁ x₁ z₂ x₂ :=
        q2P zeroP x₁ y₁ z₁ zeroP x₂ y₂ z₂
          :+ (:- q2P zeroP x₂ y₂ z₂ zeroP x₁ y₁ z₁))
      computed)
    (solveComputed 6
      (λ x₁ y₁ z₁ x₂ y₂ z₂ →
        bracket3P x₁ y₁ x₂ y₂ :=
        q3P zeroP x₁ y₁ z₁ zeroP x₂ y₂ z₂
          :+ (:- q3P zeroP x₂ y₂ z₂ zeroP x₁ y₁ z₁))
      computed)

lieBracketAntisymmetric :
  ∀ X Y → lieBracket X Y ≡ lieNegate (lieBracket Y X)
lieBracketAntisymmetric
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂) =
  su2LieExt
    (solveComputed 6
      (λ x₁ y₁ z₁ x₂ y₂ z₂ →
        bracket1P y₁ z₁ y₂ z₂ := :- bracket1P y₂ z₂ y₁ z₁)
      computed)
    (solveComputed 6
      (λ x₁ y₁ z₁ x₂ y₂ z₂ →
        bracket2P z₁ x₁ z₂ x₂ := :- bracket2P z₂ x₂ z₁ x₁)
      computed)
    (solveComputed 6
      (λ x₁ y₁ z₁ x₂ y₂ z₂ →
        bracket3P x₁ y₁ x₂ y₂ := :- bracket3P x₂ y₂ x₁ y₁)
      computed)

lieBracketAddLeft :
  ∀ X Y Z →
  lieBracket (lieAdd X Y) Z
    ≡ lieAdd (lieBracket X Z) (lieBracket Y Z)
lieBracketAddLeft
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂)
  (su2Lie x₃ y₃ z₃) =
  su2LieExt
    (solveComputed 9
      (λ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
        bracket1P (y₁ :+ y₂) (z₁ :+ z₂) y₃ z₃ :=
        bracket1P y₁ z₁ y₃ z₃ :+ bracket1P y₂ z₂ y₃ z₃)
      computed)
    (solveComputed 9
      (λ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
        bracket2P (z₁ :+ z₂) (x₁ :+ x₂) z₃ x₃ :=
        bracket2P z₁ x₁ z₃ x₃ :+ bracket2P z₂ x₂ z₃ x₃)
      computed)
    (solveComputed 9
      (λ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
        bracket3P (x₁ :+ x₂) (y₁ :+ y₂) x₃ y₃ :=
        bracket3P x₁ y₁ x₃ y₃ :+ bracket3P x₂ y₂ x₃ y₃)
      computed)

lieBracketAddRight :
  ∀ X Y Z →
  lieBracket X (lieAdd Y Z)
    ≡ lieAdd (lieBracket X Y) (lieBracket X Z)
lieBracketAddRight
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂)
  (su2Lie x₃ y₃ z₃) =
  su2LieExt
    (solveComputed 9
      (λ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
        bracket1P y₁ z₁ (y₂ :+ y₃) (z₂ :+ z₃) :=
        bracket1P y₁ z₁ y₂ z₂ :+ bracket1P y₁ z₁ y₃ z₃)
      computed)
    (solveComputed 9
      (λ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
        bracket2P z₁ x₁ (z₂ :+ z₃) (x₂ :+ x₃) :=
        bracket2P z₁ x₁ z₂ x₂ :+ bracket2P z₁ x₁ z₃ x₃)
      computed)
    (solveComputed 9
      (λ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
        bracket3P x₁ y₁ (x₂ :+ x₃) (y₂ :+ y₃) :=
        bracket3P x₁ y₁ x₂ y₂ :+ bracket3P x₁ y₁ x₃ y₃)
      computed)

lieBracketScaleLeft :
  ∀ scalar X Y →
  lieBracket (lieScale scalar X) Y
    ≡ lieScale scalar (lieBracket X Y)
lieBracketScaleLeft
  scalar (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  su2LieExt
    (solveComputed 7
      (λ scalar x₁ y₁ z₁ x₂ y₂ z₂ →
        bracket1P (scalar :* y₁) (scalar :* z₁) y₂ z₂ :=
        scalar :* bracket1P y₁ z₁ y₂ z₂)
      computed)
    (solveComputed 7
      (λ scalar x₁ y₁ z₁ x₂ y₂ z₂ →
        bracket2P (scalar :* z₁) (scalar :* x₁) z₂ x₂ :=
        scalar :* bracket2P z₁ x₁ z₂ x₂)
      computed)
    (solveComputed 7
      (λ scalar x₁ y₁ z₁ x₂ y₂ z₂ →
        bracket3P (scalar :* x₁) (scalar :* y₁) x₂ y₂ :=
        scalar :* bracket3P x₁ y₁ x₂ y₂)
      computed)

lieBracketScaleRight :
  ∀ scalar X Y →
  lieBracket X (lieScale scalar Y)
    ≡ lieScale scalar (lieBracket X Y)
lieBracketScaleRight
  scalar (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  su2LieExt
    (solveComputed 7
      (λ scalar x₁ y₁ z₁ x₂ y₂ z₂ →
        bracket1P y₁ z₁ (scalar :* y₂) (scalar :* z₂) :=
        scalar :* bracket1P y₁ z₁ y₂ z₂)
      computed)
    (solveComputed 7
      (λ scalar x₁ y₁ z₁ x₂ y₂ z₂ →
        bracket2P z₁ x₁ (scalar :* z₂) (scalar :* x₂) :=
        scalar :* bracket2P z₁ x₁ z₂ x₂)
      computed)
    (solveComputed 7
      (λ scalar x₁ y₁ z₁ x₂ y₂ z₂ →
        bracket3P x₁ y₁ (scalar :* x₂) (scalar :* y₂) :=
        scalar :* bracket3P x₁ y₁ x₂ y₂)
      computed)

lieBracketJacobi :
  ∀ X Y Z →
  lieAdd
    (lieBracket X (lieBracket Y Z))
    (lieAdd
      (lieBracket Y (lieBracket Z X))
      (lieBracket Z (lieBracket X Y)))
  ≡ su2Lie zeroR zeroR zeroR
lieBracketJacobi
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂)
  (su2Lie x₃ y₃ z₃) =
  su2LieExt
    (solveComputed 9
      (λ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
        bracket1P y₁ z₁
          (bracket2P z₂ x₂ z₃ x₃) (bracket3P x₂ y₂ x₃ y₃)
        :+ (bracket1P y₂ z₂
              (bracket2P z₃ x₃ z₁ x₁) (bracket3P x₃ y₃ x₁ y₁)
            :+ bracket1P y₃ z₃
              (bracket2P z₁ x₁ z₂ x₂) (bracket3P x₁ y₁ x₂ y₂))
        := zeroP)
      computed)
    (solveComputed 9
      (λ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
        bracket2P z₁ x₁
          (bracket3P x₂ y₂ x₃ y₃) (bracket1P y₂ z₂ y₃ z₃)
        :+ (bracket2P z₂ x₂
              (bracket3P x₃ y₃ x₁ y₁) (bracket1P y₃ z₃ y₁ z₁)
            :+ bracket2P z₃ x₃
              (bracket3P x₁ y₁ x₂ y₂) (bracket1P y₁ z₁ y₂ z₂))
        := zeroP)
      computed)
    (solveComputed 9
      (λ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ →
        bracket3P x₁ y₁
          (bracket1P y₂ z₂ y₃ z₃) (bracket2P z₂ x₂ z₃ x₃)
        :+ (bracket3P x₂ y₂
              (bracket1P y₃ z₃ y₁ z₁) (bracket2P z₃ x₃ z₁ x₁)
            :+ bracket3P x₃ y₃
              (bracket1P y₁ z₁ y₂ z₂) (bracket2P z₁ x₁ z₂ x₂))
        := zeroP)
      computed)

lieBracketSkewAdjoint :
  ∀ Y X Z →
  su2Dot (lieBracket Y X) Z
    ≡ -R (su2Dot X (lieBracket Y Z))
lieBracketSkewAdjoint
  (su2Lie x₀ y₀ z₀)
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂) =
  solveComputed 9
    (λ x₀ y₀ z₀ x₁ y₁ z₁ x₂ y₂ z₂ →
      dotP
        (bracket1P y₀ z₀ y₁ z₁)
        (bracket2P z₀ x₀ z₁ x₁)
        (bracket3P x₀ y₀ x₁ y₁)
        x₂ y₂ z₂
      :=
      :- dotP x₁ y₁ z₁
        (bracket1P y₀ z₀ y₂ z₂)
        (bracket2P z₀ x₀ z₂ x₂)
        (bracket3P x₀ y₀ x₂ y₂))
    computed

adOperator : SU2LieAlgebra → SU2LieAlgebra → SU2LieAlgebra
adOperator Y X = lieBracket Y X
