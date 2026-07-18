module DASHI.Physics.YangMills.BalabanSU2AdjointPolynomialCalculus where

------------------------------------------------------------------------
-- Finite polynomial functional calculus for the concrete su(2) adjoint map.
--
-- CMP 98 (32)--(35), (124) applies analytic functions g and g^{-1} to
-- `ad_y`.  Before introducing convergence or complex-analytic normalization,
-- the exact finite algebra is the polynomial calculus constructed here.
-- Coefficients are listed in ascending order and evaluated by Horner recursion.
--
-- No infinite-series convergence, inverse-function theorem, or source-specific
-- coefficient estimate is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( _*R_
  ; realSolverRing
  ; emptyRealVariables
  )
import Tactic.RingSolver as Solver

open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra
  ; su2Lie
  ; su2LieExt
  ; lieZero
  ; lieAdd
  ; lieScale
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
    (Solver.solve (scalar ∷ x₁ ∷ x₂ ∷ []) realSolverRing)
    (Solver.solve (scalar ∷ y₁ ∷ y₂ ∷ []) realSolverRing)
    (Solver.solve (scalar ∷ z₁ ∷ z₂ ∷ []) realSolverRing)

lieScaleCompose :
  ∀ a b X →
  lieScale a (lieScale b X)
    ≡ lieScale (a *R b) X
lieScaleCompose a b (su2Lie x y z) =
  su2LieExt
    (Solver.solve (a ∷ b ∷ x ∷ []) realSolverRing)
    (Solver.solve (a ∷ b ∷ y ∷ []) realSolverRing)
    (Solver.solve (a ∷ b ∷ z ∷ []) realSolverRing)

lieScaleCommute :
  ∀ a b X →
  lieScale a (lieScale b X)
    ≡ lieScale b (lieScale a X)
lieScaleCommute a b (su2Lie x y z) =
  su2LieExt
    (Solver.solve (a ∷ b ∷ x ∷ []) realSolverRing)
    (Solver.solve (a ∷ b ∷ y ∷ []) realSolverRing)
    (Solver.solve (a ∷ b ∷ z ∷ []) realSolverRing)

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
    (Solver.solve (a₁ ∷ b₁ ∷ c₁ ∷ d₁ ∷ []) realSolverRing)
    (Solver.solve (a₂ ∷ b₂ ∷ c₂ ∷ d₂ ∷ []) realSolverRing)
    (Solver.solve (a₃ ∷ b₃ ∷ c₃ ∷ d₃ ∷ []) realSolverRing)

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

adPolynomialConstant :
  ∀ coefficient Y X →
  adPolynomial (coefficient ∷ []) Y X
    ≡ lieScale coefficient X
adPolynomialConstant coefficient Y (su2Lie x y z) =
  su2LieExt
    (Solver.solve (coefficient ∷ x ∷ []) realSolverRing)
    (Solver.solve (coefficient ∷ y ∷ []) realSolverRing)
    (Solver.solve (coefficient ∷ z ∷ []) realSolverRing)

adPolynomialAdd :
  ∀ coefficients Y X Z →
  adPolynomial coefficients Y (lieAdd X Z)
    ≡ lieAdd
        (adPolynomial coefficients Y X)
        (adPolynomial coefficients Y Z)
adPolynomialAdd [] Y X Z =
  su2LieExt
    (Solver.solve emptyRealVariables realSolverRing)
    (Solver.solve emptyRealVariables realSolverRing)
    (Solver.solve emptyRealVariables realSolverRing)
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
    (Solver.solve emptyRealVariables realSolverRing)
    (Solver.solve emptyRealVariables realSolverRing)
    (Solver.solve emptyRealVariables realSolverRing)
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
