module DASHI.Physics.YangMills.SU2CompactLieAlgebraInstance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)

import Tactic.RingSolver as Solver

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanRealPolynomialRing using
  (_+R_; _*R_; -R_; zeroR; oneR; realSolverRing)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( SU2Quaternion
  ; su2Identity
  ; su2Multiply
  ; su2Inverse
  ; su2MultiplyAssociative
  ; su2IdentityLeft
  ; su2IdentityRight
  ; su2InverseLeft
  ; su2InverseRight
  )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra
  ; su2Lie
  ; su2LieExt
  ; lieZero
  ; lieAdd
  ; lieNegate
  ; lieScale
  )
open import DASHI.Physics.YangMills.CompactLieGroupCore
open import DASHI.Physics.YangMills.CompactLieLinearAlgebra
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact su(2) bracket in imaginary-quaternion coordinates.  The factor two is
-- the quaternion-commutator normalization [X,Y] = XY - YX.
------------------------------------------------------------------------

twoR : ℝ
twoR = oneR +R oneR

su2Bracket : SU2LieAlgebra → SU2LieAlgebra → SU2LieAlgebra
su2Bracket (su2Lie x y z) (su2Lie u v w) =
  su2Lie
    (twoR *R ((y *R w) +R (-R (z *R v))))
    (twoR *R ((z *R u) +R (-R (x *R w))))
    (twoR *R ((x *R v) +R (-R (y *R u))))

lieAddCommutative : ∀ X Y → lieAdd X Y ≡ lieAdd Y X
lieAddCommutative (su2Lie x y z) (su2Lie u v w) =
  su2LieExt
    (Solver.solve (x ∷ u ∷ []) realSolverRing)
    (Solver.solve (y ∷ v ∷ []) realSolverRing)
    (Solver.solve (z ∷ w ∷ []) realSolverRing)

lieAdditiveInverse : ∀ X → lieAdd (lieNegate X) X ≡ lieZero
lieAdditiveInverse (su2Lie x y z) =
  su2LieExt
    (Solver.solve (x ∷ []) realSolverRing)
    (Solver.solve (y ∷ []) realSolverRing)
    (Solver.solve (z ∷ []) realSolverRing)

su2BracketAlternating : ∀ X → su2Bracket X X ≡ lieZero
su2BracketAlternating (su2Lie x y z) =
  su2LieExt
    (Solver.solve (x ∷ y ∷ z ∷ []) realSolverRing)
    (Solver.solve (x ∷ y ∷ z ∷ []) realSolverRing)
    (Solver.solve (x ∷ y ∷ z ∷ []) realSolverRing)

su2BracketAddLeft :
  ∀ X Y Z →
  su2Bracket (lieAdd X Y) Z
  ≡ lieAdd (su2Bracket X Z) (su2Bracket Y Z)
su2BracketAddLeft
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂)
  (su2Lie x₃ y₃ z₃) =
  su2LieExt
    (Solver.solve (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ x₃ ∷ y₃ ∷ z₃ ∷ []) realSolverRing)
    (Solver.solve (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ x₃ ∷ y₃ ∷ z₃ ∷ []) realSolverRing)
    (Solver.solve (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ x₃ ∷ y₃ ∷ z₃ ∷ []) realSolverRing)

su2BracketAddRight :
  ∀ X Y Z →
  su2Bracket X (lieAdd Y Z)
  ≡ lieAdd (su2Bracket X Y) (su2Bracket X Z)
su2BracketAddRight
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂)
  (su2Lie x₃ y₃ z₃) =
  su2LieExt
    (Solver.solve (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ x₃ ∷ y₃ ∷ z₃ ∷ []) realSolverRing)
    (Solver.solve (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ x₃ ∷ y₃ ∷ z₃ ∷ []) realSolverRing)
    (Solver.solve (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ x₃ ∷ y₃ ∷ z₃ ∷ []) realSolverRing)

su2Jacobi :
  ∀ X Y Z →
  lieAdd (su2Bracket X (su2Bracket Y Z))
    (lieAdd (su2Bracket Y (su2Bracket Z X))
      (su2Bracket Z (su2Bracket X Y)))
  ≡ lieZero
su2Jacobi
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂)
  (su2Lie x₃ y₃ z₃) =
  su2LieExt
    (Solver.solve (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ x₃ ∷ y₃ ∷ z₃ ∷ []) realSolverRing)
    (Solver.solve (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ x₃ ∷ y₃ ∷ z₃ ∷ []) realSolverRing)
    (Solver.solve (x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ x₃ ∷ y₃ ∷ z₃ ∷ []) realSolverRing)

su2GenericGroup : Group SU2Quaternion
su2GenericGroup = record
  { identity = su2Identity
  ; multiply = su2Multiply
  ; inverse = su2Inverse
  ; multiplyAssociative = su2MultiplyAssociative
  ; identityLeft = su2IdentityLeft
  ; identityRight = su2IdentityRight
  ; inverseLeft = su2InverseLeft
  ; inverseRight = su2InverseRight
  }

su2GenericLieAlgebra : LieAlgebra SU2LieAlgebra
su2GenericLieAlgebra = record
  { zero = lieZero
  ; add = lieAdd
  ; negate = lieNegate
  ; bracket = su2Bracket
  ; addAssociative = DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier.lieAddAssociative
  ; addCommutative = lieAddCommutative
  ; zeroLeft = DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier.lieZeroLeft
  ; additiveInverse = lieAdditiveInverse
  ; bracketAlternating = su2BracketAlternating
  ; bracketAddLeft = su2BracketAddLeft
  ; bracketAddRight = su2BracketAddRight
  ; jacobi = su2Jacobi
  }

scaleZeroScalarProof : ∀ X → lieScale zeroR X ≡ lieZero
scaleZeroScalarProof = DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier.lieScaleZero

scaleOneScalarProof : ∀ X → lieScale oneR X ≡ X
scaleOneScalarProof (su2Lie x y z) =
  su2LieExt
    (Solver.solve (x ∷ []) realSolverRing)
    (Solver.solve (y ∷ []) realSolverRing)
    (Solver.solve (z ∷ []) realSolverRing)

scaleAddVectorsProof : ∀ scalar X Y →
  lieScale scalar (lieAdd X Y)
  ≡ lieAdd (lieScale scalar X) (lieScale scalar Y)
scaleAddVectorsProof scalar (su2Lie x y z) (su2Lie u v w) =
  su2LieExt
    (Solver.solve (scalar ∷ x ∷ u ∷ []) realSolverRing)
    (Solver.solve (scalar ∷ y ∷ v ∷ []) realSolverRing)
    (Solver.solve (scalar ∷ z ∷ w ∷ []) realSolverRing)

scaleAddScalarsProof : ∀ left right X →
  lieScale (left +R right) X
  ≡ lieAdd (lieScale left X) (lieScale right X)
scaleAddScalarsProof left right (su2Lie x y z) =
  su2LieExt
    (Solver.solve (left ∷ right ∷ x ∷ []) realSolverRing)
    (Solver.solve (left ∷ right ∷ y ∷ []) realSolverRing)
    (Solver.solve (left ∷ right ∷ z ∷ []) realSolverRing)

scaleAssociativeProof : ∀ left right X →
  lieScale (left *R right) X
  ≡ lieScale left (lieScale right X)
scaleAssociativeProof left right (su2Lie x y z) =
  su2LieExt
    (Solver.solve (left ∷ right ∷ x ∷ []) realSolverRing)
    (Solver.solve (left ∷ right ∷ y ∷ []) realSolverRing)
    (Solver.solve (left ∷ right ∷ z ∷ []) realSolverRing)

bracketScaleLeftProof : ∀ scalar X Y →
  su2Bracket (lieScale scalar X) Y
  ≡ lieScale scalar (su2Bracket X Y)
bracketScaleLeftProof scalar (su2Lie x y z) (su2Lie u v w) =
  su2LieExt
    (Solver.solve (scalar ∷ x ∷ y ∷ z ∷ u ∷ v ∷ w ∷ []) realSolverRing)
    (Solver.solve (scalar ∷ x ∷ y ∷ z ∷ u ∷ v ∷ w ∷ []) realSolverRing)
    (Solver.solve (scalar ∷ x ∷ y ∷ z ∷ u ∷ v ∷ w ∷ []) realSolverRing)

bracketScaleRightProof : ∀ scalar X Y →
  su2Bracket X (lieScale scalar Y)
  ≡ lieScale scalar (su2Bracket X Y)
bracketScaleRightProof scalar (su2Lie x y z) (su2Lie u v w) =
  su2LieExt
    (Solver.solve (scalar ∷ x ∷ y ∷ z ∷ u ∷ v ∷ w ∷ []) realSolverRing)
    (Solver.solve (scalar ∷ x ∷ y ∷ z ∷ u ∷ v ∷ w ∷ []) realSolverRing)
    (Solver.solve (scalar ∷ x ∷ y ∷ z ∷ u ∷ v ∷ w ∷ []) realSolverRing)

su2RealLieAlgebra : RealLieAlgebra SU2LieAlgebra su2GenericLieAlgebra
su2RealLieAlgebra = record
  { scale = lieScale
  ; scaleZeroScalar = scaleZeroScalarProof
  ; scaleOneScalar = scaleOneScalarProof
  ; scaleAddVectors = scaleAddVectorsProof
  ; scaleAddScalars = scaleAddScalarsProof
  ; scaleAssociative = scaleAssociativeProof
  ; bracketScaleLeft = bracketScaleLeftProof
  ; bracketScaleRight = bracketScaleRightProof
  }

su2AlgebraicProofLevel : ProofLevel
su2AlgebraicProofLevel = machineChecked
