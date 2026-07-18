module DASHI.Physics.YangMills.BalabanSU2LieBracket where

------------------------------------------------------------------------
-- Concrete su(2) Lie bracket.
--
-- For pure-imaginary quaternions the commutator is twice the cross product.
-- This module defines that bracket componentwise and proves its quaternion
-- commutator realization, bilinearity, antisymmetry, Jacobi identity, and the
-- invariant-inner-product skew-adjoint law.  These are the exact algebraic
-- prerequisites for the `ad_y` functions in CMP 98 (33)--(35), (124).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using ([]; _∷_)

import Tactic.RingSolver as Solver

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
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
  ; realSolverRing
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

twoR : ℝ
twoR = oneR +R oneR

lieBracket : SU2LieAlgebra → SU2LieAlgebra → SU2LieAlgebra
lieBracket
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂) =
  su2Lie
    (twoR *R ((y₁ *R z₂) +R (-R (z₁ *R y₂))))
    (twoR *R ((z₁ *R x₂) +R (-R (x₁ *R z₂))))
    (twoR *R ((x₁ *R y₂) +R (-R (y₁ *R x₂))))

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
    (Solver.solve
      (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)
    (Solver.solve
      (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)
    (Solver.solve
      (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)
    (Solver.solve
      (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)

lieBracketAntisymmetric :
  ∀ X Y → lieBracket X Y ≡ lieNegate (lieBracket Y X)
lieBracketAntisymmetric
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂) =
  su2LieExt
    (Solver.solve
      (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)
    (Solver.solve
      (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)
    (Solver.solve
      (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)

lieBracketAddLeft :
  ∀ X Y Z →
  lieBracket (lieAdd X Y) Z
    ≡ lieAdd (lieBracket X Z) (lieBracket Y Z)
lieBracketAddLeft
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂)
  (su2Lie x₃ y₃ z₃) =
  su2LieExt
    (Solver.solve
      (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ x₃ ∷ y₃ ∷ z₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ x₃ ∷ y₃ ∷ z₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ x₃ ∷ y₃ ∷ z₃ ∷ [])
      realSolverRing)

lieBracketAddRight :
  ∀ X Y Z →
  lieBracket X (lieAdd Y Z)
    ≡ lieAdd (lieBracket X Y) (lieBracket X Z)
lieBracketAddRight
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂)
  (su2Lie x₃ y₃ z₃) =
  su2LieExt
    (Solver.solve
      (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ x₃ ∷ y₃ ∷ z₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ x₃ ∷ y₃ ∷ z₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ x₃ ∷ y₃ ∷ z₃ ∷ [])
      realSolverRing)

lieBracketScaleLeft :
  ∀ scalar X Y →
  lieBracket (lieScale scalar X) Y
    ≡ lieScale scalar (lieBracket X Y)
lieBracketScaleLeft
  scalar (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  su2LieExt
    (Solver.solve
      (scalar ∷ x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)
    (Solver.solve
      (scalar ∷ x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)
    (Solver.solve
      (scalar ∷ x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)

lieBracketScaleRight :
  ∀ scalar X Y →
  lieBracket X (lieScale scalar Y)
    ≡ lieScale scalar (lieBracket X Y)
lieBracketScaleRight
  scalar (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  su2LieExt
    (Solver.solve
      (scalar ∷ x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)
    (Solver.solve
      (scalar ∷ x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)
    (Solver.solve
      (scalar ∷ x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)

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
    (Solver.solve
      (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ x₃ ∷ y₃ ∷ z₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ x₃ ∷ y₃ ∷ z₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ x₃ ∷ y₃ ∷ z₃ ∷ [])
      realSolverRing)

lieBracketSkewAdjoint :
  ∀ Y X Z →
  su2Dot (lieBracket Y X) Z
    ≡ -R (su2Dot X (lieBracket Y Z))
lieBracketSkewAdjoint
  (su2Lie x₀ y₀ z₀)
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂) =
  Solver.solve
    (x₀ ∷ y₀ ∷ z₀ ∷ x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ [])
    realSolverRing

adOperator : SU2LieAlgebra → SU2LieAlgebra → SU2LieAlgebra
adOperator Y X = lieBracket Y X
