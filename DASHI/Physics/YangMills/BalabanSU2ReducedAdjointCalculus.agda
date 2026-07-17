module DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus where

------------------------------------------------------------------------
-- Three-coefficient functional calculus for ad_y on su(2).
--
-- The cubic identity
--
--   A^3 = k A,  k = -4 <y,y>,  A = ad_y
--
-- reduces every polynomial in A to
--
--   a I + b A + c A^2.
--
-- This module constructs that reduced operator carrier and its exact
-- composition law.  It is the finite algebra needed to represent the CMP 98
-- factors g(±i ad_y), g^{-1}(±i ad_y), and exp(±i ad_y) once their scalar
-- coefficient functions and normalization are supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)

import Tactic.RingSolver as Solver

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( _+R_
  ; _*R_
  ; zeroR
  ; oneR
  ; realSolverRing
  )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra
  ; su2Lie
  ; su2LieExt
  ; lieAdd
  ; lieScale
  )
open import DASHI.Physics.YangMills.BalabanSU2LieBracket using
  ( adOperator )
open import DASHI.Physics.YangMills.BalabanSU2AdjointCubicReduction using
  ( adCubicCoefficient )

record ReducedAdjointOperator : Set where
  constructor reducedAd
  field
    identityCoefficient : ℝ
    linearCoefficient : ℝ
    quadraticCoefficient : ℝ

open ReducedAdjointOperator public

reducedAdjointExt :
  ∀ {left right : ReducedAdjointOperator} →
  identityCoefficient left ≡ identityCoefficient right →
  linearCoefficient left ≡ linearCoefficient right →
  quadraticCoefficient left ≡ quadraticCoefficient right →
  left ≡ right
reducedAdjointExt
  {reducedAd a b c} {reducedAd .a .b .c}
  refl refl refl = refl

applyReducedAdjoint :
  SU2LieAlgebra →
  ReducedAdjointOperator →
  SU2LieAlgebra →
  SU2LieAlgebra
applyReducedAdjoint Y operator X =
  lieAdd
    (lieScale (identityCoefficient operator) X)
    (lieAdd
      (lieScale (linearCoefficient operator) (adOperator Y X))
      (lieScale (quadraticCoefficient operator)
        (adOperator Y (adOperator Y X))))

identityReducedAdjoint : ReducedAdjointOperator
identityReducedAdjoint = reducedAd oneR zeroR zeroR

composeReducedAdjoint :
  SU2LieAlgebra →
  ReducedAdjointOperator →
  ReducedAdjointOperator →
  ReducedAdjointOperator
composeReducedAdjoint Y
  (reducedAd a b c)
  (reducedAd d e f) =
  reducedAd
    (a *R d)
    (((a *R e) +R (b *R d))
      +R (adCubicCoefficient Y *R
        ((b *R f) +R (c *R e))))
    (((a *R f) +R (b *R e))
      +R (c *R d)
      +R (adCubicCoefficient Y *R (c *R f)))

applyIdentityReducedAdjoint :
  ∀ Y X →
  applyReducedAdjoint Y identityReducedAdjoint X ≡ X
applyIdentityReducedAdjoint Y (su2Lie x y z) =
  su2LieExt
    (Solver.solve (x ∷ y ∷ z ∷ []) realSolverRing)
    (Solver.solve (x ∷ y ∷ z ∷ []) realSolverRing)
    (Solver.solve (x ∷ y ∷ z ∷ []) realSolverRing)

applyReducedComposition :
  ∀ Y left right X →
  applyReducedAdjoint Y left
    (applyReducedAdjoint Y right X)
  ≡
  applyReducedAdjoint Y
    (composeReducedAdjoint Y left right)
    X
applyReducedComposition
  (su2Lie y₁ y₂ y₃)
  (reducedAd a b c)
  (reducedAd d e f)
  (su2Lie x₁ x₂ x₃) =
  su2LieExt
    (Solver.solve
      (y₁ ∷ y₂ ∷ y₃ ∷ a ∷ b ∷ c ∷ d ∷ e ∷ f ∷
       x₁ ∷ x₂ ∷ x₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (y₁ ∷ y₂ ∷ y₃ ∷ a ∷ b ∷ c ∷ d ∷ e ∷ f ∷
       x₁ ∷ x₂ ∷ x₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (y₁ ∷ y₂ ∷ y₃ ∷ a ∷ b ∷ c ∷ d ∷ e ∷ f ∷
       x₁ ∷ x₂ ∷ x₃ ∷ [])
      realSolverRing)

composeReducedIdentityLeft :
  ∀ Y operator →
  composeReducedAdjoint Y identityReducedAdjoint operator ≡ operator
composeReducedIdentityLeft Y (reducedAd a b c) =
  reducedAdjointExt
    (Solver.solve
      (a ∷ b ∷ c ∷ adCubicCoefficient Y ∷ []) realSolverRing)
    (Solver.solve
      (a ∷ b ∷ c ∷ adCubicCoefficient Y ∷ []) realSolverRing)
    (Solver.solve
      (a ∷ b ∷ c ∷ adCubicCoefficient Y ∷ []) realSolverRing)

composeReducedIdentityRight :
  ∀ Y operator →
  composeReducedAdjoint Y operator identityReducedAdjoint ≡ operator
composeReducedIdentityRight Y (reducedAd a b c) =
  reducedAdjointExt
    (Solver.solve
      (a ∷ b ∷ c ∷ adCubicCoefficient Y ∷ []) realSolverRing)
    (Solver.solve
      (a ∷ b ∷ c ∷ adCubicCoefficient Y ∷ []) realSolverRing)
    (Solver.solve
      (a ∷ b ∷ c ∷ adCubicCoefficient Y ∷ []) realSolverRing)

composeReducedCommutative :
  ∀ Y left right →
  composeReducedAdjoint Y left right
    ≡ composeReducedAdjoint Y right left
composeReducedCommutative Y
  (reducedAd a b c)
  (reducedAd d e f) =
  reducedAdjointExt
    (Solver.solve
      (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ adCubicCoefficient Y ∷ [])
      realSolverRing)
    (Solver.solve
      (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ adCubicCoefficient Y ∷ [])
      realSolverRing)
    (Solver.solve
      (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ adCubicCoefficient Y ∷ [])
      realSolverRing)

composeReducedAssociative :
  ∀ Y first second third →
  composeReducedAdjoint Y
    (composeReducedAdjoint Y first second)
    third
  ≡
  composeReducedAdjoint Y
    first
    (composeReducedAdjoint Y second third)
composeReducedAssociative Y
  (reducedAd a b c)
  (reducedAd d e f)
  (reducedAd g h i) =
  reducedAdjointExt
    (Solver.solve
      (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷
       adCubicCoefficient Y ∷ [])
      realSolverRing)
    (Solver.solve
      (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷
       adCubicCoefficient Y ∷ [])
      realSolverRing)
    (Solver.solve
      (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷
       adCubicCoefficient Y ∷ [])
      realSolverRing)
