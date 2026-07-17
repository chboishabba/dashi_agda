module DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier where

------------------------------------------------------------------------
-- Concrete su(2) carrier and adjoint action.
--
-- The group SU(2) is the unit-quaternion carrier from
-- `BalabanSU2QuaternionCarrier`.  Its Lie algebra is represented by the
-- three imaginary quaternion coordinates.  The action
--
--   Ad_u X = u X conjugate(u)
--
-- is defined literally and all additive/group-action laws below are reduced
-- to polynomial identities over the same commutative-ring socket already used
-- by the quaternion carrier.  No additional postulate or analytic theorem is
-- introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (sym)

import Tactic.RingSolver as Solver

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanLatticeAdjointCovariantDerivative using
  ( AdjointAdditiveModule )
open import DASHI.Physics.YangMills.BalabanCovariantPathIntegral using
  ( AdjointLinearModule )
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
  ; realSolverRing
  ; _+q_
  ; conjugateQ
  ; _*q_
  ; SU2Quaternion
  ; su2q
  ; quaternion
  ; su2Identity
  ; su2Multiply
  ; su2QuaternionGroup
  )

record SU2LieAlgebra : Set where
  constructor su2Lie
  field
    xComponent : ℝ
    yComponent : ℝ
    zComponent : ℝ

open SU2LieAlgebra public

su2LieExt :
  ∀ {X Y : SU2LieAlgebra} →
  xComponent X ≡ xComponent Y →
  yComponent X ≡ yComponent Y →
  zComponent X ≡ zComponent Y →
  X ≡ Y
su2LieExt {su2Lie x y z} {su2Lie .x .y .z} refl refl refl = refl

lieQuaternion : SU2LieAlgebra → Quaternion
lieQuaternion (su2Lie x y z) = quat zeroR x y z

lieFromQuaternion : Quaternion → SU2LieAlgebra
lieFromQuaternion q = su2Lie (q1 q) (q2 q) (q3 q)

lieFromQuaternionLieQuaternion :
  ∀ X → lieFromQuaternion (lieQuaternion X) ≡ X
lieFromQuaternionLieQuaternion (su2Lie x y z) = refl

lieZero : SU2LieAlgebra
lieZero = su2Lie zeroR zeroR zeroR

lieAdd : SU2LieAlgebra → SU2LieAlgebra → SU2LieAlgebra
lieAdd (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  su2Lie (x₁ +R x₂) (y₁ +R y₂) (z₁ +R z₂)

lieNegate : SU2LieAlgebra → SU2LieAlgebra
lieNegate (su2Lie x y z) = su2Lie (-R x) (-R y) (-R z)

lieSubtract : SU2LieAlgebra → SU2LieAlgebra → SU2LieAlgebra
lieSubtract X Y = lieAdd X (lieNegate Y)

lieScale : ℝ → SU2LieAlgebra → SU2LieAlgebra
lieScale scalar (su2Lie x y z) =
  su2Lie (scalar *R x) (scalar *R y) (scalar *R z)

lieAddAssociative :
  ∀ X Y Z → lieAdd (lieAdd X Y) Z ≡ lieAdd X (lieAdd Y Z)
lieAddAssociative
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂)
  (su2Lie x₃ y₃ z₃) =
  su2LieExt
    (Solver.solve (x₁ ∷ x₂ ∷ x₃ ∷ []) realSolverRing)
    (Solver.solve (y₁ ∷ y₂ ∷ y₃ ∷ []) realSolverRing)
    (Solver.solve (z₁ ∷ z₂ ∷ z₃ ∷ []) realSolverRing)

lieZeroLeft : ∀ X → lieAdd lieZero X ≡ X
lieZeroLeft (su2Lie x y z) =
  su2LieExt
    (Solver.solve (x ∷ []) realSolverRing)
    (Solver.solve (y ∷ []) realSolverRing)
    (Solver.solve (z ∷ []) realSolverRing)

lieZeroRight : ∀ X → lieAdd X lieZero ≡ X
lieZeroRight (su2Lie x y z) =
  su2LieExt
    (Solver.solve (x ∷ []) realSolverRing)
    (Solver.solve (y ∷ []) realSolverRing)
    (Solver.solve (z ∷ []) realSolverRing)

adjointQuaternion :
  SU2Quaternion → SU2LieAlgebra → Quaternion
adjointQuaternion u X =
  (quaternion u *q lieQuaternion X) *q conjugateQ (quaternion u)

su2Adjoint :
  SU2Quaternion → SU2LieAlgebra → SU2LieAlgebra
su2Adjoint u X = lieFromQuaternion (adjointQuaternion u X)

adjointQuaternionPureImaginary :
  ∀ u X → q0 (adjointQuaternion u X) ≡ zeroR
adjointQuaternionPureImaginary
  (su2q (quat a₀ a₁ a₂ a₃) a-unit)
  (su2Lie x y z) =
  Solver.solve
    (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ x ∷ y ∷ z ∷ [])
    realSolverRing

lieQuaternionAdjoint :
  ∀ u X → lieQuaternion (su2Adjoint u X) ≡ adjointQuaternion u X
lieQuaternionAdjoint u X =
  DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier.quaternionExt
    (sym (adjointQuaternionPureImaginary u X))
    refl refl refl

su2AdjointUnit :
  ∀ X → su2Adjoint su2Identity X ≡ X
su2AdjointUnit (su2Lie x y z) =
  su2LieExt
    (Solver.solve (x ∷ y ∷ z ∷ []) realSolverRing)
    (Solver.solve (x ∷ y ∷ z ∷ []) realSolverRing)
    (Solver.solve (x ∷ y ∷ z ∷ []) realSolverRing)

su2AdjointMultiply :
  ∀ u v X →
  su2Adjoint (su2Multiply u v) X
    ≡ su2Adjoint u (su2Adjoint v X)
su2AdjointMultiply
  (su2q (quat a₀ a₁ a₂ a₃) a-unit)
  (su2q (quat b₀ b₁ b₂ b₃) b-unit)
  (su2Lie x y z) =
  su2LieExt
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷
       x ∷ y ∷ z ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷
       x ∷ y ∷ z ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷
       x ∷ y ∷ z ∷ [])
      realSolverRing)

su2AdjointAdd :
  ∀ u X Y →
  su2Adjoint u (lieAdd X Y)
    ≡ lieAdd (su2Adjoint u X) (su2Adjoint u Y)
su2AdjointAdd
  (su2q (quat a₀ a₁ a₂ a₃) a-unit)
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂) =
  su2LieExt
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ x₁ ∷ y₁ ∷ z₁ ∷
       x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ x₁ ∷ y₁ ∷ z₁ ∷
       x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ x₁ ∷ y₁ ∷ z₁ ∷
       x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)

su2AdjointSubtract :
  ∀ u X Y →
  su2Adjoint u (lieSubtract X Y)
    ≡ lieSubtract (su2Adjoint u X) (su2Adjoint u Y)
su2AdjointSubtract
  (su2q (quat a₀ a₁ a₂ a₃) a-unit)
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂) =
  su2LieExt
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ x₁ ∷ y₁ ∷ z₁ ∷
       x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ x₁ ∷ y₁ ∷ z₁ ∷
       x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ x₁ ∷ y₁ ∷ z₁ ∷
       x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)

su2AdjointZero : ∀ u → su2Adjoint u lieZero ≡ lieZero
su2AdjointZero (su2q (quat a₀ a₁ a₂ a₃) a-unit) =
  su2LieExt
    (Solver.solve (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) realSolverRing)
    (Solver.solve (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) realSolverRing)
    (Solver.solve (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) realSolverRing)

su2AdjointScale :
  ∀ u scalar X →
  su2Adjoint u (lieScale scalar X)
    ≡ lieScale scalar (su2Adjoint u X)
su2AdjointScale
  (su2q (quat a₀ a₁ a₂ a₃) a-unit)
  scalar
  (su2Lie x y z) =
  su2LieExt
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ scalar ∷ x ∷ y ∷ z ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ scalar ∷ x ∷ y ∷ z ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ scalar ∷ x ∷ y ∷ z ∷ [])
      realSolverRing)

su2AdjointAdditiveModule :
  AdjointAdditiveModule su2QuaternionGroup
su2AdjointAdditiveModule = record
  { Vector = SU2LieAlgebra
  ; subtract = lieSubtract
  ; action = su2Adjoint
  ; actionUnit = su2AdjointUnit
  ; actionMultiply = su2AdjointMultiply
  ; actionSubtract = su2AdjointSubtract
  }

su2AdjointLinearModule :
  AdjointLinearModule su2QuaternionGroup
su2AdjointLinearModule = record
  { additive = su2AdjointAdditiveModule
  ; zeroVector = lieZero
  ; addVector = lieAdd
  ; addAssociative = lieAddAssociative
  ; zeroLeft = lieZeroLeft
  ; zeroRight = lieZeroRight
  ; actionZero = su2AdjointZero
  ; actionAdd = su2AdjointAdd
  }
