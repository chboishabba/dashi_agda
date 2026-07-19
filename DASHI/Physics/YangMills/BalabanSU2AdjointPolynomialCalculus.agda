module DASHI.Physics.YangMills.BalabanSU2AdjointPolynomialCalculus where

------------------------------------------------------------------------
-- Finite polynomial functional calculus for the concrete su(2) adjoint map.
--
-- CMP 98 (32)--(35), (124) applies analytic functions g and g^{-1} to
-- `ad_y`. Before introducing convergence or complex-analytic normalization,
-- the exact finite algebra is the polynomial calculus constructed here.
-- Coefficients are listed in ascending order and evaluated by Horner recursion.
--
-- No infinite-series convergence, inverse-function theorem, or source-specific
-- coefficient estimate is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Algebra.Bundles using (CommutativeRing)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( _*R_
  ; zeroR
  ; zeroʳ
  ; realCommutativeRing
  )
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  (addInterchange)

private
  module RealRing = CommutativeRing realCommutativeRing

open RealRing using (distribˡ; *-assoc; *-comm)

open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra
  ; su2Lie
  ; su2LieExt
  ; lieZero
  ; lieAdd
  ; lieScale
  ; lieScaleZero
  ; lieZeroLeft
  ; lieZeroRight
  )
open import DASHI.Physics.YangMills.BalabanSU2LieBracket using
  ( lieBracketAddRight
  ; lieBracketScaleRight
  ; adOperator
  )

lieScaleAdd :
  ∀ scalar X Y →
  lieScale scalar (lieAdd X Y)
    ≡ lieAdd (lieScale scalar X) (lieScale scalar Y)
lieScaleAdd scalar
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂) =
  su2LieExt
    (distribˡ scalar x₁ x₂)
    (distribˡ scalar y₁ y₂)
    (distribˡ scalar z₁ z₂)

lieScaleCompose :
  ∀ a b X →
  lieScale a (lieScale b X)
    ≡ lieScale (a *R b) X
lieScaleCompose a b (su2Lie x y z) =
  su2LieExt
    (sym (*-assoc a b x))
    (sym (*-assoc a b y))
    (sym (*-assoc a b z))

scalarScaleCommute :
  ∀ a b x → a *R (b *R x) ≡ b *R (a *R x)
scalarScaleCommute a b x =
  trans
    (sym (*-assoc a b x))
    (trans
      (cong (λ product → product *R x) (*-comm a b))
      (*-assoc b a x))

lieScaleCommute :
  ∀ a b X →
  lieScale a (lieScale b X)
    ≡ lieScale b (lieScale a X)
lieScaleCommute a b (su2Lie x y z) =
  su2LieExt
    (scalarScaleCommute a b x)
    (scalarScaleCommute a b y)
    (scalarScaleCommute a b z)

lieAddInterchange :
  ∀ A B C D →
  lieAdd (lieAdd A B) (lieAdd C D)
    ≡ lieAdd (lieAdd A C) (lieAdd B D)
lieAddInterchange
  (su2Lie a₁ a₂ a₃)
  (su2Lie b₁ b₂ b₃)
  (su2Lie c₁ c₂ c₃)
  (su2Lie d₁ d₂ d₃) =
  su2LieExt
    (addInterchange a₁ b₁ c₁ d₁)
    (addInterchange a₂ b₂ c₂ d₂)
    (addInterchange a₃ b₃ c₃ d₃)

adPower : Nat → SU2LieAlgebra → SU2LieAlgebra → SU2LieAlgebra
adPower zero Y X = X
adPower (suc n) Y X = adOperator Y (adPower n Y X)

adPowerAdd :
  ∀ n Y X Z →
  adPower n Y (lieAdd X Z)
    ≡ lieAdd (adPower n Y X) (adPower n Y Z)
adPowerAdd zero Y X Z = refl
adPowerAdd (suc n) Y X Z =
  trans
    (cong (adOperator Y) (adPowerAdd n Y X Z))
    (lieBracketAddRight Y (adPower n Y X) (adPower n Y Z))

adPowerScale :
  ∀ n Y scalar X →
  adPower n Y (lieScale scalar X)
    ≡ lieScale scalar (adPower n Y X)
adPowerScale zero Y scalar X = refl
adPowerScale (suc n) Y scalar X =
  trans
    (cong (adOperator Y) (adPowerScale n Y scalar X))
    (lieBracketScaleRight scalar Y (adPower n Y X))

adPolynomial :
  List ℝ → SU2LieAlgebra → SU2LieAlgebra → SU2LieAlgebra
adPolynomial [] Y X = lieZero
adPolynomial (coefficient ∷ coefficients) Y X =
  lieAdd
    (lieScale coefficient X)
    (adOperator Y (adPolynomial coefficients Y X))

adOperatorZeroRight : ∀ Y → adOperator Y lieZero ≡ lieZero
adOperatorZeroRight Y =
  trans
    (cong (adOperator Y) (sym (lieScaleZero lieZero)))
    (trans
      (lieBracketScaleRight zeroR Y lieZero)
      (lieScaleZero (adOperator Y lieZero)))

adPolynomialConstant :
  ∀ coefficient Y X →
  adPolynomial (coefficient ∷ []) Y X
    ≡ lieScale coefficient X
adPolynomialConstant coefficient Y X =
  trans
    (cong (lieAdd (lieScale coefficient X)) (adOperatorZeroRight Y))
    (lieZeroRight (lieScale coefficient X))

adPolynomialAdd :
  ∀ coefficients Y X Z →
  adPolynomial coefficients Y (lieAdd X Z)
    ≡ lieAdd
        (adPolynomial coefficients Y X)
        (adPolynomial coefficients Y Z)
adPolynomialAdd [] Y X Z =
  sym (lieZeroLeft lieZero)
adPolynomialAdd (coefficient ∷ coefficients) Y X Z =
  trans
    (cong
      (λ tail →
        lieAdd
          (lieScale coefficient (lieAdd X Z))
          (adOperator Y tail))
      (adPolynomialAdd coefficients Y X Z))
    (trans
      (cong
        (lieAdd (lieScale coefficient (lieAdd X Z)))
        (lieBracketAddRight Y
          (adPolynomial coefficients Y X)
          (adPolynomial coefficients Y Z)))
      (trans
        (cong
          (λ head →
            lieAdd head
              (lieAdd
                (adOperator Y (adPolynomial coefficients Y X))
                (adOperator Y (adPolynomial coefficients Y Z))))
          (lieScaleAdd coefficient X Z))
        (lieAddInterchange
          (lieScale coefficient X)
          (lieScale coefficient Z)
          (adOperator Y (adPolynomial coefficients Y X))
          (adOperator Y (adPolynomial coefficients Y Z)))))

adPolynomialScale :
  ∀ coefficients Y scalar X →
  adPolynomial coefficients Y (lieScale scalar X)
    ≡ lieScale scalar (adPolynomial coefficients Y X)
adPolynomialScale [] Y scalar X =
  su2LieExt
    (sym (zeroʳ scalar))
    (sym (zeroʳ scalar))
    (sym (zeroʳ scalar))
adPolynomialScale (coefficient ∷ coefficients) Y scalar X =
  trans
    (cong
      (λ tail →
        lieAdd
          (lieScale coefficient (lieScale scalar X))
          (adOperator Y tail))
      (adPolynomialScale coefficients Y scalar X))
    (trans
      (cong
        (lieAdd (lieScale coefficient (lieScale scalar X)))
        (lieBracketScaleRight scalar Y
          (adPolynomial coefficients Y X)))
      (trans
        (cong
          (λ head →
            lieAdd head
              (lieScale scalar
                (adOperator Y (adPolynomial coefficients Y X))))
          (lieScaleCommute coefficient scalar X))
        (sym
          (lieScaleAdd scalar
            (lieScale coefficient X)
            (adOperator Y (adPolynomial coefficients Y X))))))
